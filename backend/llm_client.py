"""LLM → jq translation with a mock fallback that requires no API key."""
import os
from anthropic import Anthropic

_SYSTEM = """You translate natural language into jq expressions over a JSON array of user objects.
Each object has exactly two fields: name (string) and age (number).

You MUST output only a jq expression matching ONE of these four patterns:
  1. .[]
  2. .[] | select(.FIELD OP VALUE)
  3. .[] | select(.FIELD OP VALUE) | .FIELD
  4. del(.[] | select(.FIELD OP VALUE))

Allowed field names: name, age
Allowed operators: == != > >= < <=
String values must be double-quoted.

Output the jq expression and nothing else. No explanation."""

_MOCK_RULES: list[tuple[list[str], list[str], str]] = [
    (["delet", "remov"],  ["young", "< 25", "under 25", "less than 25", "below 25"],   "del(.[] | select(.age < 25))"),
    (["delet", "remov"],  ["old", "> 30", "over 30", "older than 30", "above 30"],     "del(.[] | select(.age > 30))"),
    (["name", "names"],   ["over 30", "> 30", "older than 30", "above 30"],            ".[] | select(.age > 30) | .name"),
    (["name", "names"],   ["young", "< 25", "under 25", "less than 25"],               ".[] | select(.age < 25) | .name"),
    (["alice"],           [],                                                           '.[] | select(.name == "Alice")'),
    (["bob"],             [],                                                           '.[] | select(.name == "Bob")'),
    ([],                  ["young", "< 25", "under 25", "less than 25", "below 25"],   ".[] | select(.age < 25)"),
    ([],                  ["over 30", "> 30", "older than 30", "above 30"],            ".[] | select(.age > 30)"),
    ([],                  ["over 35", "> 35", "older than 35", "above 35"],            ".[] | select(.age > 35)"),
    (["all", "every", "show", "list", "get"], ["user", "people", "person", ""],        ".[]"),
]


def _mock(nl: str) -> str:
    nl_lower = nl.lower()
    for pos_kws, neg_kws, jq in _MOCK_RULES:
        pos_match = not pos_kws or any(k in nl_lower for k in pos_kws)
        neg_match = not neg_kws or any(k in nl_lower for k in neg_kws)
        if pos_match and neg_match:
            return jq
    return ".[]"


def nl_to_jq(natural_language: str, use_mock: bool = True) -> str:
    if use_mock:
        return _mock(natural_language)

    client = Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
    msg = client.messages.create(
        model="claude-sonnet-4-6",
        max_tokens=128,
        system=_SYSTEM,
        messages=[{"role": "user", "content": natural_language}],
    )
    return msg.content[0].text.strip()
