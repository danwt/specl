"""LLM API client via OpenRouter for generating Specl specifications."""

import json
import os
import re

import httpx


class LLMClient:
    def __init__(
        self,
        api_key: str | None = None,
        model: str = "anthropic/claude-sonnet-4",
        base_url: str = "https://openrouter.ai/api/v1",
    ):
        self.api_key = api_key or os.environ.get("OPENROUTER_API_KEY", "")
        self.model = model
        self.base_url = base_url
        self.total_cost = 0.0
        self.total_calls = 0

    def _call(self, messages: list[dict], temperature: float = 0.7) -> str:
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }
        payload = {
            "model": self.model,
            "messages": messages,
            "temperature": temperature,
            "max_tokens": 4096,
        }
        resp = httpx.post(
            f"{self.base_url}/chat/completions",
            headers=headers,
            json=payload,
            timeout=120,
        )
        resp.raise_for_status()
        data = resp.json()
        self.total_calls += 1
        if "usage" in data:
            # Rough cost estimate (varies by model)
            prompt_tokens = data["usage"].get("prompt_tokens", 0)
            completion_tokens = data["usage"].get("completion_tokens", 0)
            self.total_cost += (prompt_tokens * 0.003 + completion_tokens * 0.015) / 1000
        return data["choices"][0]["message"]["content"]

    def generate_candidate(
        self,
        specl_reference: str,
        task_description: str,
        template: str | None = None,
        parents: list[str] | None = None,
        counterexamples: list[dict] | None = None,
    ) -> str:
        system = (
            "You are an expert algorithm designer. You write Specl specifications "
            "for concurrent and distributed algorithms. Your output must be a complete, "
            "syntactically valid Specl specification enclosed in ```specl ... ``` code blocks. "
            "Output ONLY the spec, no explanation."
        )
        user_parts = [
            "# Specl Language Reference\n\n" + specl_reference,
            "\n\n# Task\n\n" + task_description,
        ]

        if template:
            user_parts.append(f"\n\n# Template (fill in the marked sections)\n\n```specl\n{template}\n```")

        if parents:
            user_parts.append("\n\n# Existing verified-correct designs for reference")
            for i, p in enumerate(parents[:3]):
                user_parts.append(f"\n## Design {i + 1}\n```specl\n{p}\n```")

        if counterexamples:
            user_parts.append("\n\n# Recent failures to learn from")
            for i, ce in enumerate(counterexamples[:3]):
                user_parts.append(
                    f"\n## Failure {i + 1}\n"
                    f"Violated invariant: {ce.get('invariant', '?')}\n"
                    f"Trace:\n```\n{ce.get('trace_text', '(no trace)')}\n```\n"
                    f"Spec that failed:\n```specl\n{ce.get('spec', '(not available)')}\n```"
                )

        messages = [
            {"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user_parts)},
        ]
        return self._extract_spec(self._call(messages))

    def refine_candidate(
        self,
        specl_reference: str,
        spec: str,
        invariant: str,
        trace_text: str,
    ) -> str:
        system = (
            "You are an expert algorithm designer. You fix bugs in Specl specifications "
            "using counterexample traces. Your output must be a complete, corrected Specl "
            "specification enclosed in ```specl ... ``` code blocks. Output ONLY the spec."
        )
        user = (
            f"# Specl Language Reference\n\n{specl_reference}\n\n"
            f"# Failing Specification\n\n```specl\n{spec}\n```\n\n"
            f"# Counterexample\n\n"
            f"Violated invariant: {invariant}\n\n"
            f"Trace:\n```\n{trace_text}\n```\n\n"
            f"Analyze the counterexample, identify the root cause, and produce a corrected spec."
        )
        messages = [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ]
        return self._extract_spec(self._call(messages, temperature=0.5))

    @staticmethod
    def _extract_spec(response: str) -> str:
        # Try to extract from ```specl ... ``` blocks
        match = re.search(r"```specl\s*\n(.*?)```", response, re.DOTALL)
        if match:
            return match.group(1).strip()
        # Fallback: try generic code block
        match = re.search(r"```\s*\n(.*?)```", response, re.DOTALL)
        if match:
            return match.group(1).strip()
        # Last resort: return whole response (likely has preamble but might work)
        return response.strip()
