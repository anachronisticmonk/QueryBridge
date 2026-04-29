"""Run each buggy Lean variant against a curated input and surface
counter-examples for the gallery.

Each entry is a (binary, jq, name, description) tuple. The binary's
eval_jquery is buggy; its eval_squery is the correct one. We invoke
the binary, take the divergent output as the counter-example, and
return a list of cards for the frontend.

The seed JDB is hardcoded in each binary (matching backend.seed_data),
so the input is deterministic — what would otherwise be a Plausible
search is here a curated demonstration of the failing property.
"""
from lean_client import BIN_ERROR, BIN_BUG2, BIN_BUG3, run_binary
from seed_data import USERS


_CASES: list[dict] = [
    {
        "name": "count_returns_1",
        "title": "Count aggregate hard-coded to 1",
        "binary": BIN_ERROR,
        "jq": "length",
        "bug": "eval_jquery JQuery.count returns JResult.num 1 instead of jd.length",
        "explanation": (
            "Plausible's `prop_translation_correct` runs the jq evaluator and "
            "the SQL evaluator on equivalent databases and asserts the results "
            "agree. With this bug, the jq side returns 1 regardless of input "
            "size while the SQL side returns the true row count — the property "
            "fails on every database whose length is not 1."
        ),
    },
    {
        "name": "delete_keeps_matches",
        "title": "DELETE keeps the matches instead of dropping them",
        "binary": BIN_BUG2,
        "jq": ".[] | delete(.age > 30)",
        "bug": "eval_jquery (drop c) filters BY c instead of by ¬c — keeps the would-be deletees",
        "explanation": (
            "The jq evaluator filters the database to rows matching the predicate "
            "(the rows that should be deleted), while the SQL evaluator returns "
            "the survivors. For any input with at least one matching row, the "
            "two diverge — Plausible finds this on the smallest non-trivial DB."
        ),
    },
    {
        "name": "update_zeroes_age",
        "title": "UPDATE on age column zeroes the value",
        "binary": BIN_BUG3,
        "jq": '.[] | update(.age, 50, .name == "Alice")',
        "bug": "applyUpdate Col.age _ u writes 0 regardless of the requested value",
        "explanation": (
            "The jq update evaluator drops the value being assigned and writes "
            "zero; the SQL evaluator writes the value as requested. This is the "
            "type of bug the user gave as motivation: a transformation layer "
            "that doesn't faithfully copy the JSON value into the relational row."
        ),
    },
]


def collect_counterexamples() -> list[dict]:
    out: list[dict] = []
    for case in _CASES:
        binary = case["binary"]
        if not binary.exists():
            out.append({
                "name": case["name"],
                "title": case["title"],
                "bug": case["bug"],
                "explanation": case["explanation"],
                "jq": case["jq"],
                "jdb": USERS,
                "available": False,
                "missing_binary": binary.name,
            })
            continue
        payload = run_binary(binary, case["jq"])
        if payload is None or payload.get("match") is True:
            # Either the binary errored or the bug didn't trigger on this input.
            out.append({
                "name": case["name"],
                "title": case["title"],
                "bug": case["bug"],
                "explanation": case["explanation"],
                "jq": case["jq"],
                "jdb": USERS,
                "available": payload is not None,
                "matched": True,
            })
            continue
        out.append({
            "name": case["name"],
            "title": case["title"],
            "bug": case["bug"],
            "explanation": case["explanation"],
            "jq": case["jq"],
            "jdb": USERS,
            "available": True,
            "matched": False,
            "jq_result": payload.get("jq_result"),
            "sq_result": payload.get("sq_result"),
            "sql": payload.get("sql"),
        })
    return out
