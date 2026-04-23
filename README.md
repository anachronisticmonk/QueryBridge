# QueryBridge

**jq → SQL**, with a machine-checked proof that the two queries always return the same results.

## Project Description

QueryBridge allows users to write queries in plain English. A model converts it into a **jq** (for JSON data), and our system then translates that **jq** into an equivalent **SQL** query (for relational databases). This is useful because JSON works well for flexible, nested data, while SQL is better for fast queries and handling large datasets, so converting between them gives both flexibility and performance.

The core goal of the project is **correctness**. We use **Lean 4** to formally verify that the generated SQL query has the same meaning as the original jq.

To achieve this, we:
- Model JSON and SQL databases as separate data structures  
- Define when these databases are **equivalent**  
- Design small query languages for jq and SQL  
- Implement a translation from jq queries to SQL  

### Key Result

If the JSON and SQL databases start out equivalent, then running a jq query on the JSON database and its translated SQL query on the SQL database will produce **equivalent results**.

## Supported Queries

- `SELECT *`  
- `SELECT column`  
- `DELETE WHERE`  

(and their jq equivalents)

## Run

### Backend
```bash
cd backend
pip install -r requirements.txt
uvicorn main:app --port 8000 --reload
```

**Frontend** (separate terminal)
```bash
cd frontend
npm install
npm run dev
# → http://localhost:5173
```

The UI has a **Mock LLM** toggle (on by default) — no API key needed to try it. To use the real Claude API, copy `backend/.env.example` to `backend/.env` and set `ANTHROPIC_API_KEY`.

## Lean proof

```bash
cd ProofPilot
lake update   # one-time Mathlib fetch
lake build
```