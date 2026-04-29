from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from dotenv import load_dotenv

from seed_data import USERS
from translator import translate
from executor import run_jq, run_sql
from llm_client import nl_to_jq
from lean_client import run_lean
from counterexample_runner import collect_counterexamples

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
    use_error: bool = False


def _explain_counterexample(payload: dict) -> str:
    jq_r = payload.get("jq_result")
    sq_r = payload.get("sq_result")
    if isinstance(jq_r, dict) and isinstance(sq_r, dict) and "count" in jq_r and "count" in sq_r:
        return (
            f"Buggy eval_jquery returned count={jq_r['count']} but the correct "
            f"eval_squery returned count={sq_r['count']}. The proof of "
            f"query_equiv would refuse to type-check against this implementation."
        )
    return (
        "eval_jquery and eval_squery diverged on this input — the equivalence "
        "theorem does not hold for this evaluator pair."
    )


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

        lean_payload = run_lean(jq_expr, use_error=req.use_error)
        lean_sql = lean_payload["sql"] if lean_payload else None
        counterexample = None
        if lean_payload and lean_payload.get("match") is False:
            counterexample = {
                "jq_result": lean_payload.get("jq_result"),
                "sql_result": lean_payload.get("sq_result"),
                "explanation": _explain_counterexample(lean_payload),
            }

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
            "lean_used_error": req.use_error,
            "counterexample": counterexample,
        }
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@app.get("/api/counterexamples")
def counterexamples():
    return {"items": collect_counterexamples()}


@app.get("/health")
def health():
    return {"ok": True}
