# QueryBridge

Natural language → jq → SQL, with a machine-checked proof that the two queries always return the same results.

## Run

**Backend**
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

## How it works

1. You type a natural language query.
2. An LLM (or mock) produces a **jq** expression.
3. The jq is mechanically translated to **SQL** — this step is formally verified by theorem `query_equiv` in `ProofPilot/Main.lean` (Lean 4).
4. Both queries run on identical data; the split screen shows they return the same rows.

Supported query forms: `SELECT *`, `SELECT col`, `DELETE WHERE` — and their jq equivalents.

## Lean proof

```bash
cd ProofPilot
lake update   # one-time Mathlib fetch
lake build
```
