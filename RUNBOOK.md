# ProofPilot — Runbook

How to extend the system. Read this before touching any file.

---

## What is frozen forever

These files are **never modified** after initial setup.
If you feel the urge to edit them, the right fix is almost always in `ProofPilot/` instead.

| File | Why it's frozen |
|------|----------------|
| `app/frontend/src/**` | UI is decided. It renders whatever the backend sends. |
| `app/backend/server.js` | Thin orchestrator. Calls Claude → lean-server → jq. No logic. |
| `app/backend/routes/execute.js` | Runs jq against `users.json`. Pure I/O. |
| `app/backend/routes/verify.js` | Forwards `jquery` JSON to lean-server. No logic. |
| `app/lean-server/server.js` | Shells out to `lake exe proofpilot`. No logic. |

The backend reads `ProofPilot/query-ops.json` at **startup** to build the
Claude prompt. Restart the backend after editing that file. No code change needed.

---

## The three files you always touch together

When adding any new operation, exactly three files change — all inside `ProofPilot/`:

```
ProofPilot/
├── ProofPilot/Lang/QueryEquiv.lean   ← 1. the proof  (main work)
├── Main.lean                          ← 2. the CLI parser  (mechanical)
└── query-ops.json                     ← 3. the contract    (one entry)
```

---

## Runbook: adding `sort`

### Step 1 — `QueryEquiv.lean`: add constructors

```lean
inductive JQuery where
  | find   : (Juser → Bool) → JQuery
  | delete : (Juser → Bool) → JQuery
  | sort   : (Juser → Nat)  → JQuery   -- ← new
```

```lean
inductive SQuery where
  | select  : (Suser → Bool) → SQuery
  | drop    : (Suser → Bool) → SQuery
  | orderBy : (Suser → Nat)  → SQuery  -- ← new
```

At this point `lake build` **will fail** — that is expected and correct.
The system will show "Proof broken" on the frontend until Step 1d.

### Step 2 — `QueryEquiv.lean`: extend the translation

```lean
def jqueryToSquery : JQuery → SQuery
  | .find   p   => .select  (jpred_to_spred p)
  | .delete p   => .drop    (jpred_to_spred p)
  | .sort   key => .orderBy (fun r => key { name := r.1, age := r.2 })  -- ← new
```

```lean
def eval_jquery (jd : JDB) : JQuery → JDB
  | .find   p   => jd.filter p
  | .delete p   => jd.filter (fun u => !p u)
  | .sort   key => jd.mergeSort (fun a b => key a ≤ key b)              -- ← new
```

```lean
def eval_squery (sd : SDB) : SQuery → SDB
  | .select  p   => sd.filter p
  | .drop    p   => sd.filter (fun r => !p r)
  | .orderBy key => sd.mergeSort (fun a b => key a ≤ key b)             -- ← new
```

### Step 3 — `QueryEquiv.lean`: write the helper lemmas

Add the `@[simp]` lemmas needed for `sort` (analogous to `jdbToSdb_filter`).
Example shape:

```lean
@[simp]
theorem jdbToSdb_mergeSort (jd : JDB) (key : Juser → Nat) :
    jdbToSdb (jd.mergeSort (fun a b => key a ≤ key b)) =
    (jdbToSdb jd).mergeSort (fun r s => key {name:=r.1,age:=r.2} ≤ key {name:=s.1,age:=s.2}) := by
  induction jd with
  | nil => simp [jdbToSdb]
  | cons u us ih => sorry  -- fill in
```

Work in VS Code with the Lean extension — red squiggles tell you exactly
what's missing. `sorry` is a valid placeholder while you're developing.

### Step 4 — `QueryEquiv.lean`: extend the master theorem

```lean
theorem query_equiv1 ... := by
  ...
  | sort key =>
    simp [eval_jquery, eval_squery, jqueryToSquery]
    rw [h_to_sdb]          -- or whatever closes the goal
```

```lean
theorem query_equiv2 ... := by
  ...
  | sort key =>
    simp [eval_jquery, eval_squery, jqueryToSquery]
    rw [h_to_jdb]
```

`query_equiv` is derived from `query_equiv1` + `query_equiv2` — no change needed there.

**`lake build` passes.** The system now shows ✓ for sort queries.

### Step 5 — `Main.lean`: expose sort to the CLI

In `Concrete.toJQuery`, add a case:

```lean
def toJQuery (kind : String) (p : Pred) : Option JQuery :=
  match kind with
  | "find"   => some (.find   (evalJPred p))
  | "delete" => some (.delete (evalJPred p))
  | "sort"   => some (.sort   (fun u => evalJPred p u |>.toNat))  -- adjust as needed
  | _        => none
```

If `sort` needs a different payload shape than `Pred` (e.g. a key field
rather than a comparison), add a new parser branch in `Main.lean`.
The CLI contract stays the same: JSON in, `verified`/`out_of_scope` out.

### Step 6 — `query-ops.json`: register the operation

```json
{
  "operations": [
    { "type": "find",   "sql_equivalent": "SELECT", "description": "Return rows where predicate holds" },
    { "type": "delete", "sql_equivalent": "DELETE",  "description": "Remove rows where predicate holds" },
    { "type": "sort",   "sql_equivalent": "ORDER BY","description": "Return all rows sorted by a field" }
  ],
  "pred_fields": ["age"],
  "pred_ops": ["lt", "le", "gt", "ge", "eq", "ne"]
}
```

**Restart the backend.** Claude's prompt is rebuilt from this file at startup.
No other backend change is needed.

### Step 7 — verify end-to-end

```bash
cd ProofPilot && lake build          # must pass
# restart lean-server and backend if running
```

Try in the UI: *"sort users by age"* → should show ✓ Lean verified.

---

## Summary table

| Step | File | Who does it |
|------|------|-------------|
| Add constructors | `QueryEquiv.lean` | Lean dev |
| Extend translation + semantics | `QueryEquiv.lean` | Lean dev |
| Write helper lemmas | `QueryEquiv.lean` | Lean dev (main work) |
| Extend master theorem | `QueryEquiv.lean` | Lean dev |
| Expose to CLI | `Main.lean` | Lean dev (mechanical) |
| Register operation | `query-ops.json` | Lean dev (one JSON entry) |
| Restart backend | — | anyone |

---

## Signals during development

| `lake build` result | Frontend shows | Meaning |
|---------------------|---------------|---------|
| Passes | ✓ Lean verified | Proof complete |
| Fails | ✗ Proof broken + Lean errors | New op added, proof incomplete |
| Exe exits `out_of_scope` | ⊘ Out of proof scope | Op not in `Concrete.toJQuery` yet |
| Exe not found | ⚡ Not built | `lake build` has never run |

The "Proof broken" state is **normal and expected** between Step 1 and Step 4.
It is the system telling you the proof is in progress.

---

## Running the full stack

```bash
# Once — build the Lean project
cd ProofPilot && lake update && lake build

# Three terminals
cd app/lean-server && node server.js
cd app/backend    && node server.js   # .env needs ANTHROPIC_API_KEY
cd app/frontend   && npm run dev      # → http://localhost:5173
```

After editing `query-ops.json` or any Lean file, re-run `lake build` and
restart the backend. Frontend and lean-server do not need restarting.
