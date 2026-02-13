"""LLM-guided algorithm discovery harness for Specl.

Usage:
    uv run main.py --task crdt_counter --generations 10 --candidates 5
    uv run main.py --task crdt_set --generations 20 --candidates 8 --model anthropic/claude-sonnet-4
"""

import argparse
import json
import random
import sys
import tempfile
import time
from pathlib import Path

from llm import LLMClient
from population import Candidate, Population, new_candidate_id
from specl_runner import SpeclResult, SpeclRunner

SCRIPT_DIR = Path(__file__).parent
PROMPTS_DIR = SCRIPT_DIR / "prompts"
RESULTS_DIR = SCRIPT_DIR / "results"


# ---------- Task definitions ----------

TASKS = {
    "crdt_counter": {
        "data_type": "a counter (supports increment and decrement)",
        "data_type_description": (
            "A counter that supports Increment and Decrement operations on individual replicas. "
            "After merging, all replicas should agree on the counter value. "
            "The counter value should reflect the total increments minus total decrements across all replicas. "
            "Hint: a single integer per replica won't work because merges can't distinguish "
            "increments from decrements. Consider tracking increments and decrements separately per replica."
        ),
        "constants": {"N": 2},
        "max_states": 500_000,
    },
    "crdt_set": {
        "data_type": "a set (supports add and remove)",
        "data_type_description": (
            "A set that supports Add(element) and Remove(element) operations. "
            "After merging, all replicas should agree on set membership. "
            "Challenge: if one replica adds element X while another removes X concurrently, "
            "the merged result must be deterministic. Common strategies: tombstone sets (2P-Set), "
            "unique tags per add (OR-Set), or last-writer-wins with timestamps. "
            "Use a small element domain (0..2 or 0..3)."
        ),
        "constants": {"N": 2},
        "max_states": 500_000,
    },
    "crdt_register": {
        "data_type": "a register (supports write of a value)",
        "data_type_description": (
            "A register holding a single value that supports Write(value) operations. "
            "When concurrent writes happen on different replicas, the merged result must "
            "deterministically choose one value. Common strategies: last-writer-wins with "
            "timestamps/counters, or multi-value register (keep all concurrent values). "
            "Use a small value domain (0..2)."
        ),
        "constants": {"N": 2},
        "max_states": 500_000,
    },
}


def format_trace(result: SpeclResult) -> str:
    if not result.trace:
        return "(no trace)"
    lines = []
    for step in result.trace:
        state_str = ", ".join(f"{k}={v}" for k, v in step.state.items())
        lines.append(f"  Step {step.step}: {step.action} -> {state_str}")
    return "\n".join(lines)


def run_discovery(
    task_name: str,
    generations: int,
    candidates_per_gen: int,
    model: str,
    specl_binary: str,
    api_key: str,
    verbose: bool = False,
) -> None:
    task = TASKS[task_name]
    runner = SpeclRunner(binary=specl_binary)
    llm = LLMClient(api_key=api_key, model=model)
    pop = Population(max_size=50)

    # Load prompts
    specl_ref = (PROMPTS_DIR / "specl_reference.md").read_text()
    task_prompt_template = (PROMPTS_DIR / "crdt_task.md").read_text()
    task_prompt = task_prompt_template.format(
        data_type=task["data_type"],
        data_type_description=task["data_type_description"],
    )

    # Results directory for this run
    run_id = f"{task_name}_{int(time.time())}"
    run_dir = RESULTS_DIR / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    print(f"=== Discovery run: {run_id} ===")
    print(f"Task: {task_name}")
    print(f"Model: {model}")
    print(f"Generations: {generations}, Candidates/gen: {candidates_per_gen}")
    print(f"Results: {run_dir}")
    print()

    for gen in range(generations):
        gen_start = time.time()
        gen_safe = 0
        gen_violations = 0
        gen_errors = 0

        for ci in range(candidates_per_gen):
            cid = new_candidate_id()

            # Choose strategy
            safe_parents = pop.safe_candidates()
            failing = pop.failing_candidates()

            r = random.random()
            if safe_parents and r < 0.4:
                strategy = "vary"
            elif failing and r < 0.8:
                strategy = "refine"
            else:
                strategy = "fresh"

            # Generate spec via LLM
            try:
                if strategy == "refine" and failing:
                    target = pop.select_for_refinement()
                    spec_source = llm.refine_candidate(
                        specl_reference=specl_ref,
                        spec=target.spec_source,
                        invariant=target.invariant_violated or "unknown",
                        trace_text=target.trace_text,
                    )
                elif strategy == "vary" and safe_parents:
                    spec_source = llm.generate_candidate(
                        specl_reference=specl_ref,
                        task_description=task_prompt + (
                            "\n\nProduce a VARIATION of the existing design. "
                            "Maintain correctness but try a different approach, "
                            "simpler state, or novel conflict resolution strategy."
                        ),
                        parents=[p.spec_source for p in safe_parents[:2]],
                    )
                else:
                    spec_source = llm.generate_candidate(
                        specl_reference=specl_ref,
                        task_description=task_prompt,
                        parents=[p.spec_source for p in safe_parents[:2]] if safe_parents else None,
                    )
            except Exception as e:
                print(f"  [{gen}/{ci}] LLM error: {e}")
                gen_errors += 1
                continue

            # Write spec to temp file
            spec_file = run_dir / f"gen{gen:03d}_{cid}.specl"
            spec_file.write_text(spec_source)

            # Lint first
            lint_result = runner.lint(spec_file)
            if lint_result.result == "error":
                if verbose:
                    print(f"  [{gen}/{ci}] {cid} LINT ERROR: {lint_result.error}")
                pop.add(Candidate(
                    id=cid,
                    spec_source=spec_source,
                    generation=gen,
                    parent_id=None,
                    verification_result="error",
                    states_explored=0,
                    check_time_seconds=0,
                ))
                gen_errors += 1
                continue

            # Full model check
            check_result = runner.check(
                spec_file,
                constants=task["constants"],
                max_states=task["max_states"],
            )

            trace_text = format_trace(check_result)
            candidate = Candidate(
                id=cid,
                spec_source=spec_source,
                generation=gen,
                parent_id=None,
                verification_result=check_result.result,
                states_explored=check_result.states_explored or 0,
                check_time_seconds=check_result.duration_secs,
                invariant_violated=check_result.invariant,
                trace_text=trace_text,
            )
            pop.add(candidate)

            if check_result.is_safe:
                gen_safe += 1
                label = f"OK ({check_result.states_explored} states, {check_result.duration_secs:.1f}s)"
            elif check_result.is_violation:
                gen_violations += 1
                label = f"VIOLATION: {check_result.invariant}"
            else:
                gen_errors += 1
                label = f"{check_result.result}: {check_result.error or ''}"

            status_char = "+" if check_result.is_safe else "-" if check_result.is_violation else "!"
            print(f"  [{gen}/{ci}] {status_char} {cid} ({strategy}) {label}")

        gen_time = time.time() - gen_start
        print(
            f"Gen {gen}: safe={gen_safe} violations={gen_violations} errors={gen_errors} "
            f"({gen_time:.1f}s) | Pop: {pop.safe_count}/{pop.total} safe, "
            f"LLM cost: ${llm.total_cost:.2f}"
        )
        print()

        # Save population after each generation
        pop.save(run_dir / "population.json")

    # Final report
    print("=" * 60)
    print("DISCOVERY COMPLETE")
    print(f"Total candidates: {pop.total}")
    print(f"Safe: {pop.safe_count}")
    print(f"Violations: {pop.violation_count}")
    print(f"Errors: {pop.error_count}")
    print(f"LLM calls: {llm.total_calls}")
    print(f"Estimated cost: ${llm.total_cost:.2f}")
    print()

    safe = pop.safe_candidates()
    if safe:
        print("=== VERIFIED-SAFE CANDIDATES ===")
        for i, c in enumerate(safe[:5]):
            print(f"\n--- #{i + 1}: {c.id} (gen {c.generation}, {c.states_explored} states) ---")
            print(c.spec_source)
            # Save best candidates
            (run_dir / f"safe_{i}_{c.id}.specl").write_text(c.spec_source)
    else:
        print("No verified-safe candidates found.")


def main() -> None:
    parser = argparse.ArgumentParser(description="LLM-guided algorithm discovery with Specl")
    parser.add_argument("--task", required=True, choices=list(TASKS.keys()), help="Discovery task")
    parser.add_argument("--generations", type=int, default=10, help="Number of generations")
    parser.add_argument("--candidates", type=int, default=5, help="Candidates per generation")
    parser.add_argument("--model", default="anthropic/claude-sonnet-4", help="OpenRouter model ID")
    parser.add_argument("--specl", default="specl", help="Path to specl binary")
    parser.add_argument("--api-key", default=None, help="OpenRouter API key (or OPENROUTER_API_KEY env)")
    parser.add_argument("--verbose", action="store_true", help="Show detailed output")
    args = parser.parse_args()

    api_key = args.api_key or ""
    if not api_key:
        import os
        api_key = os.environ.get("OPENROUTER_API_KEY", "")
    if not api_key:
        print("Error: set OPENROUTER_API_KEY or pass --api-key", file=sys.stderr)
        sys.exit(1)

    run_discovery(
        task_name=args.task,
        generations=args.generations,
        candidates_per_gen=args.candidates,
        model=args.model,
        specl_binary=args.specl,
        api_key=api_key,
        verbose=args.verbose,
    )


if __name__ == "__main__":
    main()
