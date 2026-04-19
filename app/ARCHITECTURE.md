# App Architecture

## Data flow for a single query

```
"names of users under age 10"
  │
  ▼ POST /api/run
backend
  ├─ Claude → { jq, sql, jquery: { type:"find", pred:{field:"age",op:"lt",value:10} } }
  │
  ├─ POST /verify { jquery }
  │    lean-server
  │      execSync("lake exe proofpilot '...'")
  │        Main.lean: parses jquery, query_equiv applies → stdout "verified"
  │    ← { verified: true, theorem: "query_equiv", covers: "find|delete" }
  │
  └─ jq '[.[] | select(.age < 10) | .name]' users.json
       ← { ok: true, result: ["Alice","Charlie","Eve","Frank"] }
  │
  ▼ response to frontend
{ jq, sql, jquery, jqResult, verification }
```

## Verification states

| State | What it means | Who triggers it |
|-------|--------------|-----------------|
| `verified` | query_equiv proved for this JQuery | lean exe exits 0, stdout "verified" |
| `out_of_scope` | query type not in JQuery yet | lean exe or backend short-circuit |
| `proof_broken` | lake build failed | lean exe crashes, stderr has "error:" |
| `not_built` | lake build never ran | lean exe not found |

## Ports

| Service | Port |
|---------|------|
| frontend (Vite) | 5173 |
| backend (Express) | 3001 |
| lean-server (Express) | 4000 |
