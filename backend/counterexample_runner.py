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
# Pre-computed proofTrace output, written at Lean-build time. The slim
# runtime image doesn't ship `lake` (which proofTrace needs to discover
# oleans), so we serve this static snapshot instead.
PROOF_TRACE_CACHE = LEAN_DIR / "proof_trace.json"


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
    """Return the kernel-verified proof traces for each named theorem
    in `ProofPilot/Main.lean`. Each item in `items` carries:

        name, title, description, kind, type, status,
        axioms, proofTermDepth

    See ProofPilot/ProofTrace.lean for the contract.

    Resolution order:
      1. Pre-computed snapshot at `ProofPilot/proof_trace.json` if
         present — the prod Docker image bakes this at build time so
         /api/proofs works without `lake` at runtime.
      2. Live invocation of the `proofTrace` binary under `lake env`
         (dev path — needs a Lean toolchain on PATH).
    """
    # 1. Cached snapshot — serve immediately if present.
    if PROOF_TRACE_CACHE.exists():
        try:
            items = json.loads(PROOF_TRACE_CACHE.read_text(encoding="utf-8"))
            return {"available": True, "missing_binary": None, "items": items}
        except (json.JSONDecodeError, OSError):
            # Fall through to live invocation if the snapshot is unreadable.
            pass

    # 2. Live invocation via lake env.
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
