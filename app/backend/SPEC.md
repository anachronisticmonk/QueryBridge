# Backend — Spec

## Role

Express server that:
1. Calls Claude to translate NL → `{ jq, sql, simpleQuery }`
2. Sends `simpleQuery` to lean-server for proof
3. Runs jq on `data/users.json` for display
4. Returns everything to the frontend

## POST /api/run

**Request:** `{ query: "names of all users under age 10" }`

**Response:**
```json
{
  "jq":  "[.[] | select(.age < 10) | .name]",
  "sql": "SELECT name FROM users WHERE age < 10",
  "simpleQuery": { "project": "name", "filter": { "field": "age", "op": "lt", "value": 10 } },
  "jqResult":     { "ok": true, "result": ["Alice", "Charlie"] },
  "verification": { "verified": true, "theorem": "QueryEquiv.jq_sql_equiv" }
}
```

## Claude prompt contract

`generate.js` asks Claude for JSON with keys `jq`, `sql`, `simpleQuery`.
`simpleQuery` must match the schema in `CLAUDE.md`.

If Claude can't fit the query into `SimpleQuery`, it should return
`"simpleQuery": null` and the backend should skip verification.

## Environment

```
ANTHROPIC_API_KEY=...
LEAN_SERVER_URL=http://localhost:4000
MOCK_CLAUDE=false   # set true to bypass API calls
PORT=3001
```
