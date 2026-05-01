from pathlib import Path

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel
from dotenv import load_dotenv

from seed_data import USERS
from translator import translate
from executor import run_jq, run_sql
from llm_client import nl_to_jq
from lean_client import run_lean
from counterexample_runner import collect_counterexamples, collect_proof_traces
from proof_witness import build_witness

load_dotenv()

app = FastAPI(title="QueryBridge API")
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)


class QueryRequest(BaseModel):
    natural_language: str
    mock: bool = True


@app.get("/api/data")
def get_data():
    return {"users": USERS}


@app.post("/api/query")
def run_query(req: QueryRequest):
    try:
        jq_expr = nl_to_jq(req.natural_language, use_mock=req.mock)
        query = translate(jq_expr)
        jq_results = run_jq(USERS, query)
        sql_cols, sql_results = run_sql(query["sql"], USERS)

        lean_payload = run_lean(jq_expr)
        lean_sql = lean_payload["sql"] if lean_payload else None
        case_tag = lean_payload.get("jquery_case") if lean_payload else None
        proof_witness = build_witness(case_tag, lean_payload) if case_tag else None

        return {
            "jq": jq_expr,
            "sql": query["display_sql"],
            "sql_raw": query["sql"],
            "query_type": query["type"],
            "jq_results": jq_results,
            "sql_results": sql_results,
            "sql_columns": sql_cols,
            "verified": True,
            "lean_sql": lean_sql,
            "proof_witness": proof_witness,
        }
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@app.get("/api/properties")
def properties():
    """Run Plausible against the Error.lean evaluator via the
    `propRunner` Lean binary and return its structured TestResult
    JSON. See backend/counterexample_runner.py for the shape."""
    return collect_counterexamples()


@app.get("/api/proofs")
def proofs():
    """Ask the Lean kernel (via the `proofTrace` binary) to load
    Main.lean's environment, then for each named theorem report
    its statement, the axioms it transitively depends on, and
    whether `sorryAx` is in that set (`status: "verified"` iff not).
    See backend/counterexample_runner.py for the shape."""
    return collect_proof_traces()


@app.get("/health")
def health():
    return {"ok": True}


# In production (Docker) the React SPA is built into ../frontend/dist and
# served by FastAPI at "/" so the whole stack runs on a single port. In
# development the file doesn't exist; Vite serves the SPA on 5173 and
# proxies /api/* to this server, so the mount is a no-op.
_FRONTEND_DIST = Path(__file__).resolve().parent.parent / "frontend" / "dist"
if _FRONTEND_DIST.is_dir():
    app.mount("/", StaticFiles(directory=str(_FRONTEND_DIST), html=True), name="frontend")
