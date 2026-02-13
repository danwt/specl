"""Evolutionary population of candidate algorithms."""

import json
import random
import uuid
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Candidate:
    id: str
    spec_source: str
    generation: int
    parent_id: str | None
    verification_result: str  # "ok" | "invariant_violation" | "deadlock" | "error" | "timeout"
    counterexample: dict | None = None
    states_explored: int = 0
    check_time_seconds: float = 0.0
    invariant_violated: str | None = None
    trace_text: str = ""

    @property
    def is_safe(self) -> bool:
        return self.verification_result == "ok"


class Population:
    def __init__(self, max_size: int = 50):
        self.candidates: list[Candidate] = []
        self.max_size = max_size

    def add(self, candidate: Candidate) -> None:
        self.candidates.append(candidate)
        if len(self.candidates) > self.max_size:
            self._evict()

    def _evict(self) -> None:
        # Keep all safe candidates; evict worst unsafe ones
        safe = [c for c in self.candidates if c.is_safe]
        unsafe = [c for c in self.candidates if not c.is_safe]
        # Sort unsafe by generation (keep newer ones)
        unsafe.sort(key=lambda c: c.generation, reverse=True)
        keep_unsafe = self.max_size - len(safe)
        if keep_unsafe < 0:
            # Too many safe candidates — keep best by states explored
            safe.sort(key=lambda c: c.states_explored, reverse=True)
            self.candidates = safe[: self.max_size]
        else:
            self.candidates = safe + unsafe[:keep_unsafe]

    def safe_candidates(self) -> list[Candidate]:
        return sorted(
            [c for c in self.candidates if c.is_safe],
            key=lambda c: (-c.states_explored, len(c.spec_source)),
        )

    def failing_candidates(self) -> list[Candidate]:
        return [c for c in self.candidates if c.verification_result == "invariant_violation"]

    def select_parents(self, n: int) -> list[Candidate]:
        safe = self.safe_candidates()
        if safe:
            return safe[:n]
        # No safe candidates yet — return recent failing ones as negative examples
        return []

    def select_for_refinement(self) -> Candidate | None:
        failing = self.failing_candidates()
        if not failing:
            return None
        # Prefer more recent failures
        return random.choice(failing[-5:])

    @property
    def total(self) -> int:
        return len(self.candidates)

    @property
    def safe_count(self) -> int:
        return len([c for c in self.candidates if c.is_safe])

    @property
    def violation_count(self) -> int:
        return len([c for c in self.candidates if c.verification_result == "invariant_violation"])

    @property
    def error_count(self) -> int:
        return len([c for c in self.candidates if c.verification_result in ("error", "timeout")])

    def save(self, path: Path) -> None:
        data = []
        for c in self.candidates:
            data.append({
                "id": c.id,
                "spec_source": c.spec_source,
                "generation": c.generation,
                "parent_id": c.parent_id,
                "verification_result": c.verification_result,
                "states_explored": c.states_explored,
                "check_time_seconds": c.check_time_seconds,
                "invariant_violated": c.invariant_violated,
            })
        path.write_text(json.dumps(data, indent=2))

    @classmethod
    def load(cls, path: Path, max_size: int = 50) -> "Population":
        pop = cls(max_size=max_size)
        data = json.loads(path.read_text())
        for d in data:
            pop.candidates.append(Candidate(
                id=d["id"],
                spec_source=d["spec_source"],
                generation=d["generation"],
                parent_id=d.get("parent_id"),
                verification_result=d["verification_result"],
                states_explored=d.get("states_explored", 0),
                check_time_seconds=d.get("check_time_seconds", 0.0),
                invariant_violated=d.get("invariant_violated"),
            ))
        return pop


def new_candidate_id() -> str:
    return uuid.uuid4().hex[:8]
