# Training Data

This directory holds all datasets used for model training and evaluation.
It is intentionally kept separate from the Lean source code so that:

- The lake build does not pick up `.jsonl` / `.csv` files.
- Dataset versions can be managed independently (e.g. DVC, Git LFS).
- The code stays clean; data pipelines stay auditable.

## Directory layout

```
data/
├── raw/          # Lean source files extracted verbatim from LeanLangur
├── examples/     # Curated (problem, proof) pairs in JSONL format
└── processed/    # Tokenised / split datasets ready for training
```

## Format — `examples/*.jsonl`

Each line is a JSON object:

```json
{
  "id": "bintree_mem_001",
  "type": "theorem",
  "imports": ["Mathlib"],
  "statement": "theorem mem_iff_mem_toList ...",
  "proof": "by induction t with ...",
  "tactics": ["grind", "simp"],
  "tags": ["data-structures", "induction", "grind"]
}
```

## Generating data

```bash
python scripts/extract_examples.py \
  --src ../ProofPilot \
  --out data/raw \
  --format jsonl
```
