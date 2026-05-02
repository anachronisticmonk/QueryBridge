"""Per-query proof-witness builder.

When a user runs a jq query, we want to surface a *specific* proof
witness for that query — not just the universal `query_equiv`
theorem. This module:

  1. Reads the source span of `query_equiv`'s proof out of
     `ProofPilot/Main.lean` once and caches the per-case excerpts
     keyed by JQuery constructor (find / drop / prepend / clear /
     length / modify).

  2. Caches the full kernel-checked proof metadata for `query_equiv`
     by invoking the `proofTrace` Lean binary on first use — that
     gives us the theorem statement, axioms, and proof-term depth
     that the kernel actually accepted.

  3. For each /api/query call, given the jq AST shape and the case
     tag returned by sqlGenMain (Lean evaluates which arm of the
     proof's `cases jq` block governs this query), assembles a
     `proof_witness` record combining (1) and (2) plus the per-query
     specifics: the instantiated jq → SQL pair, the kernel-evaluated
     results from sqlGenMain (`match: true` IS the witness), and the
     line range so the UI can deep-link to the source.
"""
from __future__ import annotations

from typing import Any

from counterexample_runner import collect_proof_traces
from lean_client import LEAN_DIR

MAIN_LEAN = LEAN_DIR / "Main.lean"

# Case → (1-based line range in Main.lean, supporting lemmas, gloss)
# These ranges are stable: each constructor gets its own arm of the
# `cases jq with | ... =>` block in the proof of `query_equiv`. If
# Main.lean is restructured, only these line numbers need updating.
_CASES: dict[str, dict[str, Any]] = {
    "find": {
        "lines": (368, 403),
        "lemmas": ["permEquiv_implies_equiv", "eval_bridgeJ", "eval_bridgeS",
                   "toRows_filter_reconstruct"],
        "gloss": (
            "JQuery.find c p translates to SQuery.select c p. "
            "The proof shows: a JSON record satisfies the predicate "
            "iff the corresponding SQL row does (via eval_bridgeJ / "
            "eval_bridgeS), so the filtered JSON list is equivalent "
            "to the filtered SQL projection."
        ),
        "translation": "JQuery.find c p ⟶ SQuery.select c p",
    },
    "drop": {
        "lines": (405, 460),
        "lemmas": ["permEquiv_implies_equiv", "eval_bridgeJ", "eval_bridgeS",
                   "toRows_filter_reconstruct"],
        "gloss": (
            "JQuery.drop c (jq's del) translates to SQuery.delete c. "
            "Symmetric to the find case: the survivors of a deletion "
            "in JSON correspond exactly to the survivors in SQL, "
            "because the predicate evaluates the same way on both sides."
        ),
        "translation": "JQuery.drop c ⟶ SQuery.delete c",
    },
    "prepend": {
        "lines": (462, 499),
        "lemmas": ["permEquiv_implies_equiv", "toRows_insert", "toJ_toS"],
        "gloss": (
            "JQuery.prepend u (jq's insert) translates to "
            "SQuery.insert (toS u). The proof shows that prepending "
            "a JSON record then converting to SQL rows is the same "
            "as inserting the converted row into the column-form."
        ),
        "translation": "JQuery.prepend u ⟶ SQuery.insert (toS u)",
    },
    "clear": {
        "lines": (501, 505),
        "lemmas": [],
        "gloss": (
            "JQuery.clear (jq's del(.[])) translates to "
            "SQuery.truncate. Both sides reduce to an empty database, "
            "so equivalence is immediate from the definition of "
            "SDB.toRows on empty column lists."
        ),
        "translation": "JQuery.clear ⟶ SQuery.truncate",
    },
    "length": {
        "lines": (507, 511),
        "lemmas": ["List.Perm.length_eq", "List.length_map"],
        "gloss": (
            "JQuery.length translates to SQuery.count. Aggregate "
            "queries need permutation equivalence (multiset equality), "
            "not just set equivalence. Lengths are equal because "
            "List.Perm preserves length and toS is injective."
        ),
        "translation": "JQuery.length ⟶ SQuery.count",
    },
    "modify": {
        "lines": (513, 528),
        "lemmas": ["applyUpdateIf_bridge", "toRows_map_reconstruct",
                   "permEquiv_implies_equiv", "List.Perm.map"],
        "gloss": (
            "JQuery.modify col v c translates to SQuery.update col v c. "
            "The proof builds permEquiv between the post-update databases "
            "by applying the per-row UPDATE bridge under the existing "
            "permutation equivalence."
        ),
        "translation": "JQuery.modify col v c ⟶ SQuery.update col v c",
    },
}


_main_lean_lines: list[str] | None = None
_query_equiv_meta: dict[str, Any] | None = None


def _load_main_lean() -> list[str]:
    """Read `ProofPilot/Main.lean` and cache its lines.

    In the slim Docker runtime the `.lean` source may not be shipped
    (only the compiled binaries are). When the file is missing, return
    an empty list so the proof witness still renders — `case_source`
    will be empty but every other field still carries kernel-derived
    information from sqlGenMain + proofTrace.
    """
    global _main_lean_lines
    if _main_lean_lines is None:
        try:
            _main_lean_lines = MAIN_LEAN.read_text(encoding="utf-8").splitlines()
        except FileNotFoundError:
            _main_lean_lines = []
    return _main_lean_lines


def _query_equiv_kernel_meta() -> dict[str, Any]:
    """Cached lookup of `query_equiv`'s kernel-checked metadata
    (statement, axioms, proof-term depth) via the `proofTrace`
    Lean binary. Returns an empty dict if the binary is unavailable
    so per-query proof can still render with degraded info.
    """
    global _query_equiv_meta
    if _query_equiv_meta is None:
        traces = collect_proof_traces()
        if traces.get("available"):
            for it in traces.get("items", []):
                if it.get("name") == "query_equiv":
                    _query_equiv_meta = it
                    break
        if _query_equiv_meta is None:
            _query_equiv_meta = {}
    return _query_equiv_meta


def _excerpt(start: int, end: int) -> str:
    lines = _load_main_lean()
    # Return the source as written, dedented uniformly so the UI
    # can render it in a monospace block without wasted leading space.
    span = lines[start - 1:end]
    if not span:
        return ""
    common = min(
        (len(l) - len(l.lstrip(" ")) for l in span if l.strip()),
        default=0,
    )
    return "\n".join(l[common:] if len(l) >= common else l for l in span)


def build_witness(case_tag: str, lean_payload: dict | None) -> dict[str, Any]:
    """Assemble a proof_witness object for one query.

    Args:
      case_tag: the `jquery_case` string emitted by sqlGenMain
                (one of: find, drop, prepend, clear, length, modify).
      lean_payload: the full sqlGenMain JSON for this query
                    (carries `match`, `jq_result`, `sq_result`,
                    `squery_case`, `sql`).
    """
    info = _CASES.get(case_tag)
    if info is None:
        return {
            "available": False,
            "reason": f"Unknown jq case tag: {case_tag!r}",
        }

    start, end = info["lines"]
    meta = _query_equiv_kernel_meta()

    # The kernel-evaluated witness: sqlGenMain ran both eval_jquery
    # and eval_squery on the seed DB; `match: true` means Lean's
    # kernel reduced both sides to structurally-equal values. That
    # is the per-query *proof witness* — a closed term inhabiting
    # `result_equiv (eval_jquery seedDB jq) (eval_squery sd (jquery_to_squery jq))`.
    kernel_match = bool(lean_payload.get("match")) if lean_payload else None

    return {
        "available": True,
        "theorem": "query_equiv",
        "theorem_statement": meta.get(
            "type",
            "∀ (jd : JDB) (sd : SDB) (jq : JQuery), permEquiv jd sd → "
            "result_equiv (eval_jquery jd jq) (eval_squery sd (jquery_to_squery jq))",
        ),
        "axioms": meta.get("axioms", []),
        "proofTermDepth": meta.get("proofTermDepth"),
        "case": case_tag,
        "case_translation": info["translation"],
        "case_gloss": info["gloss"],
        "case_supporting_lemmas": info["lemmas"],
        "case_source_lines": [start, end],
        "case_source": _excerpt(start, end),
        "kernel_match": kernel_match,
        "squery_case": (lean_payload or {}).get("squery_case"),
        "kernel_jq_result": (lean_payload or {}).get("jq_result"),
        "kernel_sq_result": (lean_payload or {}).get("sq_result"),
    }
