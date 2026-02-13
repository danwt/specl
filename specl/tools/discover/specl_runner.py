"""Invoke the Specl CLI and parse structured JSON output."""

import json
import subprocess
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class TraceStep:
    step: int
    action: str
    state: dict[str, str]


@dataclass
class SpeclResult:
    result: str  # "ok" | "invariant_violation" | "deadlock" | "error" | "timeout" | "state_limit_reached" | "memory_limit_reached"
    states_explored: int | None = None
    max_depth: int | None = None
    duration_secs: float = 0.0
    invariant: str | None = None
    trace: list[TraceStep] = field(default_factory=list)
    error: str | None = None
    raw_stdout: str = ""
    raw_stderr: str = ""

    @classmethod
    def from_json(cls, stdout: str, stderr: str = "") -> "SpeclResult":
        try:
            data = json.loads(stdout)
        except (json.JSONDecodeError, ValueError):
            return cls(
                result="error",
                error=f"Failed to parse JSON output: {stdout[:500]}",
                raw_stdout=stdout,
                raw_stderr=stderr,
            )

        trace = []
        if data.get("trace"):
            for i, step in enumerate(data["trace"]):
                trace.append(TraceStep(
                    step=i,
                    action=step.get("action", "?"),
                    state=step.get("state", {}),
                ))

        return cls(
            result=data.get("result", "unknown"),
            states_explored=data.get("states_explored"),
            max_depth=data.get("max_depth"),
            duration_secs=data.get("duration_secs", 0.0),
            invariant=data.get("invariant"),
            trace=trace,
            error=data.get("error"),
            raw_stdout=stdout,
            raw_stderr=stderr,
        )

    @classmethod
    def timeout(cls) -> "SpeclResult":
        return cls(result="timeout")

    @property
    def is_safe(self) -> bool:
        return self.result == "ok"

    @property
    def is_violation(self) -> bool:
        return self.result == "invariant_violation"

    @property
    def is_error(self) -> bool:
        return self.result in ("error", "timeout")


class SpeclRunner:
    def __init__(self, binary: str = "specl"):
        self.binary = binary

    def lint(self, spec_path: str | Path, timeout_secs: int = 5) -> SpeclResult:
        cmd = [self.binary, "lint", str(spec_path), "--output", "json"]
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                timeout=timeout_secs,
                text=True,
            )
            return SpeclResult.from_json(proc.stdout, proc.stderr)
        except subprocess.TimeoutExpired:
            return SpeclResult.timeout()
        except FileNotFoundError:
            return SpeclResult(result="error", error=f"Binary not found: {self.binary}")

    def check(
        self,
        spec_path: str | Path,
        constants: dict[str, int] | None = None,
        max_states: int = 500_000,
        timeout_secs: int = 30,
        no_deadlock: bool = True,
    ) -> SpeclResult:
        cmd = [
            self.binary, "check", str(spec_path),
            "--output", "json",
            "--no-auto",
            "--max-states", str(max_states),
        ]
        if no_deadlock:
            cmd.append("--no-deadlock")
        for k, v in (constants or {}).items():
            cmd.extend(["-c", f"{k}={v}"])

        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                timeout=timeout_secs,
                text=True,
            )
            return SpeclResult.from_json(proc.stdout, proc.stderr)
        except subprocess.TimeoutExpired:
            return SpeclResult.timeout()
        except FileNotFoundError:
            return SpeclResult(result="error", error=f"Binary not found: {self.binary}")

    def simulate(
        self,
        spec_path: str | Path,
        constants: dict[str, int] | None = None,
        steps: int = 100,
        seed: int | None = None,
        timeout_secs: int = 10,
    ) -> SpeclResult:
        cmd = [
            self.binary, "simulate", str(spec_path),
            "--output", "json",
            "--steps", str(steps),
        ]
        if seed is not None:
            cmd.extend(["--seed", str(seed)])
        for k, v in (constants or {}).items():
            cmd.extend(["-c", f"{k}={v}"])

        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                timeout=timeout_secs,
                text=True,
            )
            return SpeclResult.from_json(proc.stdout, proc.stderr)
        except subprocess.TimeoutExpired:
            return SpeclResult.timeout()
        except FileNotFoundError:
            return SpeclResult(result="error", error=f"Binary not found: {self.binary}")
