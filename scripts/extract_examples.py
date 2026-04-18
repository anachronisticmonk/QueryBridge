#!/usr/bin/env python3
"""
extract_examples.py — Parse Lean 4 source files and emit training examples.

Usage:
    python scripts/extract_examples.py --src ProofPilot --out data/raw
"""
import argparse
import json
import re
from pathlib import Path


THEOREM_RE = re.compile(
    r"(?P<kind>theorem|lemma|example|def)\s+(?P<name>\S+).*?:=\s*by\s+(?P<proof>.+?)(?=\n\n|\Z)",
    re.DOTALL,
)
IMPORT_RE = re.compile(r"^import\s+(\S+)", re.MULTILINE)
TAG_MAP = {
    "grind":    ["grind"],
    "simp":     ["simp"],
    "StateM":   ["state-monad"],
    "induction":["induction"],
    "LinearOrder": ["type-class-polymorphism"],
}


def extract_file(path: Path) -> list[dict]:
    src = path.read_text(encoding="utf-8")
    imports = IMPORT_RE.findall(src)
    examples = []
    for m in THEOREM_RE.finditer(src):
        proof  = m.group("proof").strip()
        tactics = [t for k, ts in TAG_MAP.items() if k in proof for t in ts]
        tags    = list({t for k, ts in TAG_MAP.items() if k in src for t in ts})
        examples.append({
            "id":        f"{path.stem}_{len(examples):03d}",
            "type":      m.group("kind"),
            "file":      str(path),
            "imports":   imports,
            "statement": m.group(0).split(":= by")[0].strip(),
            "proof":     proof,
            "tactics":   tactics,
            "tags":      tags,
        })
    return examples


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="ProofPilot", help="Root source directory")
    ap.add_argument("--out", default="data/raw",   help="Output directory")
    ap.add_argument("--format", choices=["jsonl", "json"], default="jsonl")
    args = ap.parse_args()

    src_dir = Path(args.src)
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)

    all_examples: list[dict] = []
    for lean_file in sorted(src_dir.rglob("*.lean")):
        examples = extract_file(lean_file)
        all_examples.extend(examples)
        print(f"  {lean_file}: {len(examples)} examples")

    out_path = out_dir / f"examples.{args.format}"
    with out_path.open("w") as f:
        if args.format == "jsonl":
            for ex in all_examples:
                f.write(json.dumps(ex) + "\n")
        else:
            json.dump(all_examples, f, indent=2)

    print(f"\nWrote {len(all_examples)} examples → {out_path}")


if __name__ == "__main__":
    main()
