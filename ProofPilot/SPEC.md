# ProofPilot — Spec

## Role: the proof is the gatekeeper

`query_equiv` in `QueryEquiv.lean` must compile for ANY query to be verified.
A failing `lake build` is a meaningful signal — it means a new operation was
added to `JQuery`/`SQuery` but its proof hasn't been written yet.

## CLI contract

```
lake exe proofpilot '<jquery JSON>'
```

stdout line 1:
- `verified`     — query_equiv covers this JQuery
- `out_of_scope` — type not in Concrete.toJQuery
- (nothing)      — build failed (lean-server catches the exec error)

## Extending the proof

When adding `sort` (example):

```lean
-- 1. Add constructors
inductive JQuery where | ... | sort : (Juser → Nat) → JQuery
inductive SQuery where | ... | orderBy : (Suser → Nat) → SQuery

-- 2. Translation
def jqueryToSquery : JQuery → SQuery
  | ... | .sort key => .orderBy (fun r => key {name:=r.1, age:=r.2})

-- 3. Semantics
def eval_jquery jd | ... | .sort key => jd.mergeSort (fun a b => key a ≤ key b)
def eval_squery sd | ... | .orderBy key => sd.mergeSort (fun a b => key a ≤ key b)

-- 4. Extend the proof (query_equiv1, query_equiv2, query_equiv)
-- 5. Add to Concrete.toJQuery and Main.lean parser
```

## Build

```bash
lake update   # once
lake build
```
