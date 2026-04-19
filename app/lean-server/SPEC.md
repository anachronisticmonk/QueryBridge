# lean-server — Spec

## Role

Thin HTTP wrapper around the ProofPilot Lean executable.
Does NOT contain any proof logic itself.

## Endpoint

```
POST /verify
Body: { simpleQuery: { project, filter: { field, op, value } } }
```

**Success response:**
```json
{ "verified": true, "theorem": "QueryEquiv.jq_sql_equiv", "detail": "..." }
```

**Not-built response (503):**
```json
{ "error": "ProofPilot not built", "hint": "Run: cd ProofPilot && lake build" }
```

## How it works

```js
execSync(`cd ProofPilot && lake exe proofpilot '${queryJson}'`)
```

Parses stdout: first line "verified" → `verified: true`.

## ProofPilot path

Resolved as `../../ProofPilot` relative to `lean-server/server.js`.
