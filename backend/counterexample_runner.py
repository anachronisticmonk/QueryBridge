"""Lean-driven backends for the QueryBridge UI.

Two endpoints are surfaced:

  1. `collect_counterexamples()` runs the `propRunner` Lean binary,
     which executes each property in `ProofPilot/Properties.lean`
     against the deliberately-buggy `eval_jquery` from
     `ProofPilot/Error.lean`, captures the `Plausible.TestResult`,
     and prints it as JSON. The Python side just parses the JSON.

  2. `collect_proof_traces()` runs the `proofTrace` Lean binary,
     which uses `Lean.importModules` to load the kernel-checked
     environment for `ProofPilot/Main.lean` at *runtime*, queries
     each named theorem's `ConstantInfo`, pretty-prints the type
     via `Meta.ppExpr`, and walks the proof term with
     `Lean.collectAxioms` to enumerate the axioms it transitively
     depends on. A theorem is reported `verified` iff `sorryAx` is
     not in its axiom set — the same criterion the Lean kernel uses.

Both binaries serve as a single-shot RPC: we ask Lean to do the
work and hand back a structured JSON object. The kernel does the
checking; Python only marshals.
"""
import json
import subprocess

from lean_client import LEAN_DIR

BIN_PROP_RUNNER = LEAN_DIR / ".lake" / "build" / "bin" / "propRunner"
BIN_PROOF_TRACE = LEAN_DIR / ".lake" / "build" / "bin" / "proofTrace"


def collect_counterexamples() -> dict:
    """Invoke propRunner and return:
        {
          "available": bool,
          "missing_binary": str | None,
          "items": list[dict]   # one per property
        }
    Each item shape mirrors PropRunner.lean's runOne output:
      id, title, prop, description, bug, status,
      counterExample?, shrinks?, gaveUpAfter?
    """
    if not BIN_PROP_RUNNER.exists():
        return {
            "available": False,
            "missing_binary": BIN_PROP_RUNNER.name,
            "items": [],
        }
    try:
        proc = subprocess.run(
            [str(BIN_PROP_RUNNER)],
            capture_output=True,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired:
        return {
            "available": False,
            "missing_binary": None,
            "items": [],
            "error": "propRunner timed out (>120s)",
        }
    if proc.returncode != 0:
        return {
            "available": False,
            "missing_binary": None,
            "items": [],
            "error": (proc.stderr or proc.stdout or "non-zero exit").strip()[:1000],
        }
    try:
        items = json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        return {
            "available": False,
            "missing_binary": None,
            "items": [],
            "error": f"propRunner stdout was not JSON: {e}",
        }
    return {"available": True, "missing_binary": None, "items": items}


def collect_proof_traces() -> dict:
    """Invoke `proofTrace` (under `lake env`, so the binary can find
    `Main.olean` and its transitive package oleans on LEAN_PATH) and
    return the kernel-verified proof traces for each named theorem
    in `ProofPilot/Main.lean`. Each item in `items` carries:

        name, title, description, kind, type, status,
        axioms, proofTermDepth

    See ProofPilot/ProofTrace.lean for the contract.
    """
    if not BIN_PROOF_TRACE.exists():
        return {
            "available": False,
            "missing_binary": BIN_PROOF_TRACE.name,
            "items": [],
        }
    try:
        proc = subprocess.run(
            ["lake", "env", str(BIN_PROOF_TRACE)],
            cwd=str(LEAN_DIR),
            capture_output=True,
            text=True,
            timeout=60,
        )
    except FileNotFoundError:
        return {
            "available": False,
            "missing_binary": None,
            "items": [],
            "error": "lake not found on PATH — cannot set LEAN_PATH for proofTrace.",
        }
    except subprocess.TimeoutExpired:
        return {
            "available": False,
            "missing_binary": None,
            "items": [],
            "error": "proofTrace timed out (>60s)",
        }
    if proc.returncode != 0:
        return {
            "available": False,
            "missing_binary": None,
            "items": [],
            "error": (proc.stderr or proc.stdout or "non-zero exit").strip()[:1000],
        }
    try:
        items = json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        return {
            "available": False,
            "missing_binary": None,
            "items": [],
            "error": f"proofTrace stdout was not JSON: {e}",
        }
    return {"available": True, "missing_binary": None, "items": items}
