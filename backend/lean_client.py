"""Invoke the Lean executables (sqlGenMain / sqlGenError) and return parsed JSON.

The binaries are built by `lake build sqlGenMain sqlGenError` from the
ProofPilot package. If they don't exist (no Lean toolchain or no build
yet), `run_lean` returns None and the caller degrades gracefully.
"""
import json
import re
import subprocess
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent / "ProofPilot"
BIN_MAIN = LEAN_DIR / ".lake" / "build" / "bin" / "sqlGenMain"
BIN_ERROR = LEAN_DIR / ".lake" / "build" / "bin" / "sqlGenError"


def _normalize(jq_expr: str) -> str:
    """Bridge surface-syntax differences between Python's and Lean's jq parsers.

    Python (translator.py + mock LLM):  del(.[] | select(...))
    Lean   (jqToJQuery in Main.lean):   .[] | delete(...)
    """
    m = re.match(r'\s*del\(\s*(\.\[\]\s*\|\s*select\((.+)\))\s*\)\s*$', jq_expr)
    if m:
        return f".[] | delete({m.group(2)})"
    return jq_expr


def run_lean(jq_expr: str, use_error: bool = False) -> dict | None:
    binary = BIN_ERROR if use_error else BIN_MAIN
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
