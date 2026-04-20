from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from dotenv import load_dotenv

from seed_data import USERS
from translator import translate
from executor import run_jq, run_sql
from llm_client import nl_to_jq

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
        return {
            "jq": jq_expr,
            "sql": query["display_sql"],
            "sql_raw": query["sql"],
            "query_type": query["type"],
            "jq_results": jq_results,
            "sql_results": sql_results,
            "sql_columns": sql_cols,
            "verified": True,
        }
    except ValueError as e:
        raise HTTPException(status_code=400, detail=str(e))


@app.get("/health")
def health():
    return {"ok": True}
