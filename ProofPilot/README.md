# ProofPilot

Lean 4 proof that jq and SQL queries are semantically equivalent.
This is the only folder being actively developed — everything else in the repo is frozen.

## What it does

The frontend asks Claude to translate a natural-language query into both jq and SQL.
ProofPilot proves they mean the same thing, for every possible database, not just the test data.
If the proof compiles, the UI shows ✓ verified. If not, it shows exactly why.

## Layout

```
ProofPilot/
├── ProofPilot/Lang/QueryEquiv.lean  ← the proof (work here)
├── Main.lean                         ← CLI called by lean-server
├── query-ops.json                    ← operations Claude knows about
├── lakefile.toml
└── lean-toolchain                    ← pinned to v4.29.0
```

## The proof in one line

```lean
theorem query_equiv (jd : JDB) (sd : SDB) (jq : JQuery) (h : equiv jd sd) :
    equiv (eval_jquery jd jq) (eval_squery sd (jqueryToSquery jq))
```

`JDB` is a JSON store, `SDB` is a SQL store, `equiv` means they roundtrip each other.
The theorem says: run any query on both sides, they stay equivalent.

## Build

```bash
lake update   # once — fetches Mathlib
lake build
```

## Adding a new operation

See `RUNBOOK.md` at the repo root.
Short version: extend `JQuery`/`SQuery` and `query_equiv` in `QueryEquiv.lean`,
add a case to `Main.lean`, add one entry to `query-ops.json`, restart the backend.
