# Hackathon — CLAUDE.md

## What this project is

From `notes.org`: **Domain-specific output verification** — verify AI-generated
queries in the SQL/jq domain using Lean 4 as the proof engine.

---

## The proof — source of truth

`ProofPilot/ProofPilot/Lang/QueryEquiv.lean` is the file everything else
moves around. Do not restructure it; extend it.

### Types

```lean
structure Juser where name : String; age : Nat
def JDB := List Juser          -- JSON side

def Suser := String × Nat      -- SQL side  
def SDB   := List Suser

def equiv (jd : JDB) (sd : SDB) : Prop :=
  (jdbToSdb jd = sd) ∧ (sdbToJdb sd = jd)
```

### Query languages (extend these as the project grows)

```lean
inductive JQuery where
  | find   : (Juser → Bool) → JQuery   -- SELECT
  | delete : (Juser → Bool) → JQuery   -- DELETE
  -- add: sort, groupBy, limit, ...

inductive SQuery where
  | select : (Suser → Bool) → SQuery
  | drop   : (Suser → Bool) → SQuery
  -- mirror JQuery additions here
```

### The master theorem

```lean
theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jqueryToSquery jq))
```

**If this theorem does not compile, `lake build` fails → lean-server returns
`proof_broken` → frontend shows "Proof broken" red banner.**

---

## Architecture: how Lean gates the whole system

```
User NL query
  │
  ▼
BACKEND (Express :3001)
  │  Claude → { jq, sql, jquery: { type, pred } }
  │
  ├─► lean-server :4000
  │     execSync("lake exe proofpilot '<jquery json>'")
  │     ┌─ "verified"      → query_equiv covers it
  │     ├─ "out_of_scope"  → query type not in JQuery yet
  │     └─ exec error      → lake build failed (proof broken)
  │
  └─► jq CLI → results (display only)
  │
  ▼
FRONTEND
  ├─ jq query   │ sql query    (split panes)
  └─ Verification widget:
       ✓  verified         — lean-server returned "verified"
       ⊘  out_of_scope     — query not in JQuery constructors
       ✗  proof_broken     — lake build failed
       ⚡ not_built        — lake build never ran
```

---

## JQuery JSON schema (sent from backend → lean-server → ProofPilot)

```json
{ "type": "find" | "delete", "pred": { "field": "age", "op": "lt", "value": 10 } }
```

`op` ∈ `lt | le | gt | ge | eq | ne`

If Claude cannot express the query as a single-predicate JQuery, it returns
`jquery: null` and the backend short-circuits to `out_of_scope`.

---

## How to add a new operation (e.g. sort)

1. Add to `QueryEquiv.lean`:
   ```lean
   inductive JQuery where
     | ...
     | sort : (Juser → Nat) → JQuery   -- new
   inductive SQuery where
     | ...
     | orderBy : (Suser → Nat) → SQuery
   ```
2. Extend `jqueryToSquery`, `eval_jquery`, `eval_squery`.
3. Add the case to `query_equiv1`, `query_equiv2`, `query_equiv`.
4. Until step 3 is done, `lake build` fails → system shows "proof_broken".
5. Add `"sort"` to `Concrete.toJQuery` and update `Main.lean` parser.
6. Update Claude prompt to include `"sort"` as a valid `jquery.type`.

---

## Directory layout

```
hackathon/
├── notes.org              ← hackathon brief
├── LeanLangur/            ← reference (read-only)
├── bits-and-branches/     ← reference (read-only)
│
├── ProofPilot/            ← LEAN VERIFIER (source of truth)
│   ├── SPEC.md
│   ├── Main.lean          ← CLI entrypoint
│   ├── ProofPilot/
│   │   ├── Basic.lean
│   │   └── Lang/
│   │       ├── QueryEquiv.lean  ← THE proof file
│   │       └── Examples.lean
│   └── lakefile.toml
│
└── app/
    ├── ARCHITECTURE.md
    ├── frontend/          ← React :5173
    ├── backend/           ← Express :3001
    │   ├── SPEC.md
    │   └── routes/generate.js  verify.js  execute.js
    └── lean-server/       ← Express :4000 → shells into ProofPilot
        └── SPEC.md
```

---

## Run order

```bash
cd ProofPilot && lake update && lake build   # once
cd app/lean-server && node server.js
cd app/backend    && node server.js          # needs .env ANTHROPIC_API_KEY
cd app/frontend   && npm run dev
```
