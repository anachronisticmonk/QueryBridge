"""Invoke the verified Lean executable (sqlGenMain) and return parsed
JSON.

The binary is built by `lake build sqlGenMain` from the ProofPilot
package. If it doesn't exist (no Lean toolchain or no build yet),
`run_lean` returns None and the caller degrades gracefully.

The buggy-variant binaries (sqlGenError / sqlGenBug2 / sqlGenBug3)
that previously fed the per-query "use buggy variant" toggle are no
longer driven from this module. The buggy semantics now live in
ProofPilot/Error.lean and are exercised programmatically through
the propRunner binary (see counterexample_runner.py).
"""
import json
import re
import subprocess
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent / "ProofPilot"
BIN_DIR = LEAN_DIR / ".lake" / "build" / "bin"
BIN_MAIN = BIN_DIR / "sqlGenMain"


def _normalize(jq_expr: str) -> str:
    """Bridge surface-syntax differences between Python's and Lean's jq parsers.

    Python (translator.py + mock LLM):  del(.[] | select(...))   |  del(.[])
    Lean   (jqToJQuery in JqGenMain):   .[] | delete(...)        |  .[] | delete(.[])
    """
    if re.match(r'\s*del\(\s*\.\[\]\s*\)\s*$', jq_expr):
        return ".[] | delete(.[])"
    m = re.match(r'\s*del\(\s*(\.\[\]\s*\|\s*select\((.+)\))\s*\)\s*$', jq_expr)
    if m:
        return f".[] | delete({m.group(2)})"
    return jq_expr


def run_binary(binary: Path, jq_expr: str) -> dict | None:
    """Invoke an arbitrary lean binary; return parsed JSON or None."""
    if not binary.exists():
        return None
    normalized = _normalize(jq_expr)
    try:
        proc = subprocess.run(
            [str(binary), normalized],
            capture_output=True,
            text=True,
            timeout=5,
        )
    except subprocess.TimeoutExpired:
        return None
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None


def run_lean(jq_expr: str) -> dict | None:
    return run_binary(BIN_MAIN, jq_expr)
