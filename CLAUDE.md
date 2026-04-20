# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Running the app

Two processes must run in parallel:

```bash
# Terminal 1 — backend (from /backend)
cd backend && uvicorn main:app --port 8000 --reload

# Terminal 2 — frontend (from /frontend)
cd frontend && npm run dev
# → http://localhost:5173
```

The Vite dev server proxies `/api/*` to `http://localhost:8000`, so no CORS configuration is needed in development.

Backend deps: `pip install -r backend/requirements.txt`
Frontend deps: `cd frontend && npm install`

## Environment

Copy `backend/.env.example` to `backend/.env` and set `ANTHROPIC_API_KEY` to use the real LLM. The UI has a "Mock LLM" toggle (on by default) that works without any API key.

## Project purpose

QueryBridge proves that a restricted subset of **jq queries** (over JSON) are semantically equivalent to **SQL queries** (over relational data). The proof is machine-checked in Lean 4 (`ProofPilot/Main.lean`).

The app makes this tangible:
1. User types natural language → LLM produces a jq expression (unverified)
2. jq is mechanically translated to SQL via the mapping in `translator.py` (mirrors the Lean proof)
3. Both queries run on identical data; split-screen shows identical results
4. The jq→SQL arrow in the UI is labelled "Lean Verified ✓"

## Architecture

```
backend/
  main.py         FastAPI app; single POST /api/query endpoint
  translator.py   jq string → SQL string (mirrors Lean's jqueryToSquery)
  executor.py     run_jq() and run_sql() on the in-memory seed dataset
  llm_client.py   Claude API call or mock fallback (nl_to_jq)
  seed_data.py    7 hardcoded users (name + age) used by both sides

frontend/src/
  App.tsx                     State, layout, API call
  components/QueryInput.tsx   Textarea + example buttons + mock toggle
  components/Pipeline.tsx     Three-box NL→jq→SQL pipeline visualisation
  components/SplitResults.tsx Split-panel table rendering

ProofPilot/Main.lean   Lean 4 proof of query_equiv theorem
```

## Supported query subset

The translator and executor handle exactly what the Lean proof covers:

| jq pattern | SQL equivalent |
|---|---|
| `.[]` | `SELECT * FROM users` |
| `.[] \| select(.f op v)` | `SELECT * FROM users WHERE f op v` |
| `.[] \| select(.f op v) \| .col` | `SELECT col FROM users WHERE f op v` |
| `del(.[] \| select(.f op v))` | `DELETE FROM users WHERE f op v` — survivors returned |

Operators: `==  !=  >  >=  <  <=`. String values must be double-quoted in jq.

## Lean build

```bash
cd ProofPilot
lake update   # one-time Mathlib fetch
lake build
```

Lean version pinned to `leanprover/lean4:v4.29.0`. Mathlib locked to `v4.29.0` in `lakefile.toml`.
