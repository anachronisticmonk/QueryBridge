# ProofPilot

A Lean 4 proof-synthesis toolkit built for the Claude Hackathon.
ProofPilot combines a curated library of formal proofs with a structured
training-data pipeline so that language models can learn to write and
verify Lean 4 code.

---

## Repository layout

```
ProofPilot/
├── lakefile.toml              # Lake (Lean build tool) configuration
├── lean-toolchain             # Pinned Lean version (v4.29.0 + Mathlib)
├── ProofPilot.lean            # Library root — re-exports all modules
├── Main.lean                  # Executable entry point
│
├── ProofPilot/                # ── SOURCE CODE ──────────────────────────
│   ├── Basic.lean             #   Shared imports & macro overrides
│   │
│   ├── Monads/
│   │   ├── FibMemo.lean       #   Memoised Fibonacci via StateM
│   │   └── StackMachine.lean  #   Verified stack machine + ValidProgram
│   │
│   ├── DataStructures/
│   │   ├── BinTree.lean       #   BinTree with membership ↔ toList proof
│   │   └── QuickSort.lean     #   Type-polymorphic quicksort (LinearOrder)
│   │
│   ├── Tactics/
│   │   ├── GrindExamples.lean #   Showcase of the `grind` tactic
│   │   └── TypeClasses.lean   #   Type-class polymorphism patterns
│   │
│   └── Lang/
│       ├── ImpLang.lean       #   Shallow-embedded imperative DSL (IMP)
│       └── Examples.lean      #   `#run` and `eval%` usage demos
│
├── data/                      # ── TRAINING DATA (separate from code) ───
│   ├── README.md              #   Dataset format specification
│   ├── examples/
│   │   └── seed.jsonl         #   Seed (problem, proof) pairs
│   ├── raw/                   #   Auto-extracted from source (gitignored)
│   └── processed/             #   Tokenised splits (gitignored)
│
└── scripts/
    └── extract_examples.py    #   Extracts theorems from .lean → JSONL
```

---

## Key concepts covered

### State Monads
`Monads/FibMemo.lean` — `StateM (HashMap Nat Nat)` carries a memoisation
cache through the computation.  The interpreter in `Lang/ImpLang.lean` uses
`StateT ImpState TermElabM` to thread variable bindings during macro
elaboration.

### Type-Class Polymorphism
`DataStructures/QuickSort.lean` works over any `[LinearOrder α]`.
`Tactics/TypeClasses.lean` walks from explicit type arguments through
implicit arguments, auto-parameters, derived instances, and custom
type-class definitions with instances for compound types.

### Grind Tactic
`@[grind .]` annotations on definitions and theorems feed lemmas into
Lean 4's built-in ground-truth oracle.  `Tactics/GrindExamples.lean`
demonstrates arithmetic, propositional logic, and inductive-type cases.
`DataStructures/BinTree.lean` and `Monads/StackMachine.lean` close all
proofs with plain `grind` calls backed by the annotated lemma set.

### Embedded DSL (ImpLang)
`Lang/ImpLang.lean` is a *shallow embedding*: Lean's meta-programming
layer (`TermElabM`, `declare_syntax_cat`, `elab`) turns IMP programs
into Lean elaboration actions at compile time.  The `#run` command
executes a program and prints the final variable state; `eval%` lifts
the final state back into a Lean term.

---

## Getting started

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- The correct toolchain is pinned in `lean-toolchain`; elan installs it
  automatically on first `lake build`.

### Build

```bash
cd ProofPilot
lake update        # fetch Mathlib (one-time, ~few minutes)
lake build         # compile all modules
```

### Run

```bash
lake exe proofpilot
```

### Extract training examples

```bash
python scripts/extract_examples.py \
  --src ProofPilot \
  --out data/raw \
  --format jsonl
```

---

## Training data

All datasets live under `data/` and are kept **separate from the Lean
source** by design:

| Path | Contents | Tracked in git? |
|------|----------|-----------------|
| `data/examples/seed.jsonl` | Hand-curated seed examples | Yes |
| `data/raw/` | Auto-extracted from source | No (gitignored) |
| `data/processed/` | Tokenised / train-val-test splits | No (gitignored) |

Each JSONL record has the shape:

```json
{
  "id":        "bintree_mem_001",
  "type":      "theorem",
  "imports":   ["Mathlib"],
  "statement": "theorem mem_iff_mem_toList ...",
  "proof":     "by induction t with ...",
  "tactics":   ["grind", "induction"],
  "tags":      ["data-structures", "grind"]
}
```

---

## Contributing

1. Add new Lean modules under `ProofPilot/`.
2. Re-export them from `ProofPilot.lean`.
3. Run `python scripts/extract_examples.py` to refresh `data/raw/`.
4. Curate interesting examples into `data/examples/seed.jsonl`.

---

## License

MIT
