# QueryBridge

Natural-language → jq + SQL, equivalence-checked by Lean 4.

```
┌─────────────────────────────────────────────────────────┐
│  "names of all users under the age of 10"    [Run]      │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────┬───────────────────────────────┐
│  jq                     │  SQL                          │
│  .[] | select(.age<10)  │  SELECT name FROM users       │
│  | .name                │  WHERE age < 10               │
│                         │                               │
│  Results                │  Results                      │
│  Alice / Charlie / Eve  │  Alice / Charlie / Eve        │
└─────────────────────────┴───────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│  ✓  Equivalent — Lean verified                          │
└─────────────────────────────────────────────────────────┘
```

## Services

| Service | Port | Purpose |
|---------|------|---------|
| `frontend` | 5173 | React UI (Vite) |
| `backend`  | 3001 | Express: Claude API + jq + SQLite |
| `lean-server` | 4000 | Lean proof checker (placeholder) |

## Prerequisites

- Node 18+
- `jq` CLI installed (`brew install jq`)
- An `ANTHROPIC_API_KEY`

## Running locally

```bash
# 1. Lean server (placeholder)
cd lean-server
npm install
node server.js

# 2. Backend (new terminal)
cd backend
cp .env.example .env          # fill in ANTHROPIC_API_KEY
npm install
node server.js

# 3. Frontend (new terminal)
cd frontend
npm install
npm run dev
```

Open http://localhost:5173

## Wiring up the real Lean proof

`lean-server/server.js` — replace the `POST /verify` handler.
The endpoint receives:
```json
{ "jqResult": [...], "sqlResult": [...] }
```
and should return:
```json
{ "verified": true,  "proof": "..." }
// or
{ "verified": false, "counterexamples": [{ "jq": ..., "sql": ... }] }
```
