# QueryBridge

**Verified jq → SQL translation, kernel-checked in Lean 4.**

Type a query in plain English. A model produces a [jq](https://jqlang.org/)
expression over the JSON view of the data; QueryBridge translates that jq into
the equivalent SQL over the relational/columnar view; both queries run on
identical seed data and the answers are shown side-by-side. The translation is
**proven correct in Lean 4** — every theorem behind it is kernel-checked, and
every property the proof should rule out is randomly stress-tested by
[Plausible](https://github.com/leanprover-community/plausible).

---

## Why this exists — data lakes need a verified bridge

Modern data-lake architectures keep two views of the same data:

- **JSON / document layer** — flexible nested records. Cheap to evolve. The
  natural query language is jq.
- **Parquet / columnar layer** — column-pruning, vectorised scans, and
  predicate push-down make analytical queries orders of magnitude faster.
  The natural query language is SQL.

Engineers routinely write the same logical query in both layers — a jq
filter for an ad-hoc inspection, a SQL aggregate for the dashboard — and the
two had better agree. *Silently divergent* translations are the worst kind of
bug because both sides "look right" on small inputs and only disagree on the
edge cases that drive the production decision.

QueryBridge attacks this with a mechanically-checked correspondence:

> **Theorem `query_equiv`.** For every JSON database `jd`, every SQL database
> `sd` that is permutation-equivalent to it, and every supported jq query
> `jq`: evaluating `jq` against `jd` and evaluating `jquery_to_squery jq`
> against `sd` produce equivalent results.

The proof is in `ProofPilot/Main.lean`; the kernel-tracked axiom set is the
three Lean foundational axioms (`propext`, `Quot.sound`, `Classical.choice`)
and nothing else. The same `jquery_to_squery` function the proof reasons
about is the *actual* translator that ships in the binary, so the proof's
guarantee is not aspirational — it bears on every query the user runs.

---

## End-to-end demo

![QueryBridge UI](figures/end_to_end_ui.png)

A typical run:

1. The user types *"delete all users"*.
2. The mock LLM (or, with `ANTHROPIC_API_KEY` set, the live model) emits the
   jq expression `del(.[])`.
3. The Python translator emits `DELETE FROM users`.
4. The verified Lean binary `sqlGenMain` parses the *same* jq, applies the
   proven `jquery_to_squery`, and emits its own SQL string. The two strings
   should agree; the UI shows both side-by-side and tags the verified
   arrow `✓ Proven`.
5. Both queries run against identical seed data; the result panels show 0
   rows on both sides.
6. The **per-query proof witness** below the results identifies the exact
   arm of `query_equiv` that fires (`JQuery.clear ⟶ SQuery.truncate`,
   `Main.lean:501–505`), the supporting lemmas, the kernel-tracked axiom
   set, and `kernel_match: true` — the kernel reduced both sides to
   structurally-equal values for *this* specific input.

---

## Architecture

```
   ┌──────────────┐   POST /api/query     ┌────────────────┐  argv     ┌──────────────────────┐
   │  React SPA   │  ──────────────────▶  │    FastAPI     │  ───────▶ │   sqlGenMain         │
   │  (Vite)      │  ◀──────────────────  │    backend     │  ◀──────  │   (Lean kernel)      │
   └──────┬───────┘   proof_witness JSON  └───────┬────────┘   JSON    └──────────────────────┘
          │                                       │                     parses jq, applies the
          │  GET /api/properties                  │  subprocess         proven jquery_to_squery,
          │  GET /api/proofs                      │                     evaluates both sides,
          ▼                                       ▼                     emits kernel_match flag
   ┌──────────────┐                       ┌────────────────┐
   │ tabs:        │                       │  propRunner    │  argv     ┌──────────────────────┐
   │  · Query     │                       │  proofTrace    │  ───────▶ │  Plausible.checkIO   │
   │  · Proofs    │                       │  (Lean exes)   │  ◀──────  │  Lean.collectAxioms  │
   │  · Property  │                       └────────────────┘   JSON    │  Meta.ppExpr         │
   │     tests    │                                                    └──────────────────────┘
   └──────────────┘
```

- **`sqlGenMain`** (per query) — `ProofPilot/SqlGenMain.lean`. Takes a jq
  string, parses to `JQuery`, applies the proven `jquery_to_squery`, prints
  the SQL, evaluates both sides on the seed database, and returns whether
  they structurally match.
- **`propRunner`** (on demand) — `ProofPilot/PropRunner.lean`. Calls
  `Plausible.Testable.checkIO` on each property in `Properties.lean` against
  the *deliberately buggy* `eval_jquery` from `Error.lean`; returns each
  `TestResult` (success / gaveUp / failure-with-counter-example) as JSON.
- **`proofTrace`** (on demand) — `ProofPilot/ProofTrace.lean`. Loads
  `Main.olean` at runtime via `Lean.importModules`, walks each named
  theorem with `Lean.collectAxioms`, pretty-prints the type with
  `Meta.ppExpr`, and emits a structured JSON report.

The Python backend is *not* doing any proof reasoning. It marshals JSON
between the React SPA and the three Lean binaries; the Lean kernel is the
authority for everything labelled "verified" in the UI. Inside the Lean
infoview the same proof states look like this:

![Lean infoview proof state](figures/proof_window.png)

---

## The conversation, in detail

### 5.1 Per-query verified-SQL flow — `POST /api/query`

| Hop | Producer | Output |
|---|---|---|
| 1 | `frontend/src/api.ts:runQuery` | `{natural_language, mock}` |
| 2 | `backend/main.py:run_query` calls `nl_to_jq` then `translate` then `run_lean` | invokes `sqlGenMain <jq>` |
| 3 | `ProofPilot/SqlGenMain.lean:main` | `{sql, jq, jq_result, sq_result, match, jquery_case, squery_case}` |
| 4 | `backend/proof_witness.py:build_witness` enriches step 3 | adds `{theorem, theorem_statement, axioms, proofTermDepth, case_translation, case_gloss, case_supporting_lemmas, case_source_lines, case_source, kernel_match, kernel_jq_result, kernel_sq_result}` |
| 5 | Returned to `frontend/src/components/ProofWitnessPanel.tsx` | rendered as the "Per-query proof witness" panel |

The key emission from Lean is `match` (renamed `kernel_match` in the
backend) — `true` iff `eval_jquery seedDB jq` and
`eval_squery sd (jquery_to_squery jq)` reduce to structurally equal values.
That is the actual per-query *proof witness*: a closed term inhabiting the
specific instance of `result_equiv` that the universal theorem governs.

The Python side never re-derives this. It maps the `jquery_case` tag (one
of `find / drop / prepend / clear / length / modify`) to the corresponding
arm of the `cases jq` block in `Main.lean`'s proof of `query_equiv`, reads
that source span from disk, and ships it to the UI alongside the supporting
lemmas the case relies on. The mapping table lives in
`backend/proof_witness.py:_CASES`.

### 5.2 Property-based testing flow — `GET /api/properties`

| Hop | Producer | Output |
|---|---|---|
| 1 | `frontend/src/components/PropertyResults.tsx` mounts | calls `fetchProperties()` |
| 2 | `backend/main.py:properties` → `counterexample_runner.collect_counterexamples` | spawns `propRunner` |
| 3 | `ProofPilot/PropRunner.lean:main` calls `Testable.checkIO` per property | per-item: `{id, title, prop, description, bug, status, counterExample?, shrinks?, gaveUpAfter?}` |
| 4 | `PropertyResults.tsx` | renders one card per property; failures show the shrunk counter-example |

Four properties are checked, defined in `ProofPilot/Properties.lean`:

| Property | What it asserts | Bug it catches in `Error.lean` |
|---|---|---|
| `prop_modify_preserves_count` | `JQuery.modify` never changes row count | `eval_jquery (modify _ _ _) = JResult.db []` |
| `prop_length_returns_count`   | `JQuery.length` returns `jd.length`     | `eval_jquery length = JResult.num 1` (constant) |
| `prop_translation_correct`    | Headline jq ↔ SQL equivalence (boolean) | Triggered by *any* of the three bugs |
| `prop_find_always_is_identity`| `JQuery.find Col.all Cond.always = jd`  | `eval_jquery (find _ c) = jd.filter (¬c)` (predicate inverted) |

#### 5.2.1 Why the counter-examples are real

`PropRunner.lean` runs each property with Plausible's default
`Configuration{}` — no `randomSeed` is fixed. Plausible's RNG is initialised
from system entropy at process start, so successive runs find *different*
shrunk minimums for the same property. That is the same behaviour you see
opening `Test.lean` in the Lean editor, which calls `Testable.check` (not
`checkIO`) with the same default config. The counter-examples are not
hard-coded; the property is genuinely false on `Error.lean`'s
`eval_jquery`, so every run finds *some* witness.

### 5.3 Verified-theorems flow — `GET /api/proofs`

| Hop | Producer | Output |
|---|---|---|
| 1 | `frontend/src/components/ProofResults.tsx` mounts | calls `fetchProofs()` |
| 2 | `backend/main.py:proofs` → `collect_proof_traces` | spawns `lake env proofTrace` |
| 3 | `ProofPilot/ProofTrace.lean:main` does `importModules`, `Meta.ppExpr`, `Lean.collectAxioms` | per-theorem: `{name, title, description, kind, type, status, axioms, proofTermDepth}` |
| 4 | `ProofResults.tsx` | renders one card per theorem; chips for each axiom; sorry warning if `sorryAx ∈ axioms` |

`status` is `verified` iff `sorryAx` is **not** in the transitive axiom set
the kernel computed — the same criterion `#print axioms` uses. The seven
curated theorems are listed in `ProofTrace.lean:thmSpecs`; the headline
`query_equiv` rests on the three Lean foundational axioms (`propext`,
`Quot.sound`, `Classical.choice`) and nothing else.

![Proofs tab](figures/proof_trace.png)

---

## Counter-example flow — the punchline of property-based testing

The standalone story behind §5.2: *we never write the counter-examples by hand*.

`Error.lean` is a near-duplicate of `Main.lean` with three deliberate bugs
seeded into `eval_jquery`:

```lean
-- ProofPilot/Error.lean:178–187
def eval_jquery (jd : JDB) : JQuery → JResult
  | JQuery.find _ c       => JResult.db (jd.filter (fun u => !c.evalJ u))  -- !!BUG!! predicate inverted
  | JQuery.drop c         => JResult.db (jd.filter (fun u => !(c.evalJ u)))
  | JQuery.prepend u      => JResult.db (u :: jd)
  | JQuery.clear          => JResult.db []
  | JQuery.length         => JResult.num 1                                 -- !!BUG!! constant 1
  | JQuery.modify _ _ _   => JResult.db []                                 -- !!BUG!! drops everything
```

Each of the four properties in `Properties.lean` is universally quantified
(`∀ jd col v c, …`, `∀ jd jq, …`). Plausible randomly samples from
`Arbitrary` instances for `JDB`, `JQuery`, etc., and shrinks any failure
to a minimal counter-example. Open `Test.lean` in your editor and the
Lean infoview shows the raw output:

![Plausible counter-example in the Lean editor](figures/plausible.png)

Hit the *Property tests* tab in the UI for the structured form:

![Property tests tab](figures/plausible_ui.png)

The user inspecting QueryBridge never has to *construct* a database that
falsifies the property. The runtime is *search*. The proof of `query_equiv`
in `Main.lean` is what guarantees Plausible can't find any counter-example
when run against the *correct* `eval_jquery` from `Main.lean` — and the
intentional bugs in `Error.lean` are how we demonstrate the search
machinery actually works.

---

## Per-query proof witness — what's proven *for this query*

The companion to the counter-example flow. When the user runs a specific
query, the UI doesn't show "the proof of `query_equiv`" in some abstract
sense — it shows the *case of the proof* that governs this query, the
specific lemmas it depends on, and the kernel's verdict for *this* input.

![Lean infoview during a per-query proof](figures/proof_window_ii.png)

The proof of `query_equiv` is by `cases jq`: each `JQuery` constructor gets
its own arm. `sqlGenMain` reports which constructor your jq parsed to;
`backend/proof_witness.py` looks the line range up:

| Query type | jq case | SQuery case | `Main.lean` line span |
|---|---|---|---|
| `find`    | `JQuery.find c p`     | `SQuery.select c p`     | 368–403 |
| `drop`    | `JQuery.drop p`       | `SQuery.delete p`       | 405–460 |
| `prepend` | `JQuery.prepend u`    | `SQuery.insert (toS u)` | 462–499 |
| `clear`   | `JQuery.clear`        | `SQuery.truncate`       | 501–505 |
| `length`  | `JQuery.length`       | `SQuery.count`          | 507–511 |
| `modify`  | `JQuery.modify col v c` | `SQuery.update col v c` | 513–528 |

The `kernel_match` flag in the response comes from sqlGenMain actually
running both `eval_jquery` and `eval_squery` on the seed data and comparing
the structural results. For all six cases against the *correct* `Main.lean`
evaluator, `kernel_match` is always `true` — which is the per-query
inhabitant of `result_equiv (eval_jquery seedDB jq) (eval_squery sd (jquery_to_squery jq))`.

---

## Supported queries

| jq pattern | SQL equivalent |
|---|---|
| `.[]` | `SELECT * FROM users` |
| `.[] \| select(.f op v)` | `SELECT * FROM users WHERE f op v` |
| `.[] \| select(.f op v) \| .col` | `SELECT col FROM users WHERE f op v` |
| `del(.[] \| select(.f op v))` | `DELETE FROM users WHERE f op v` — survivors returned |
| `del(.[])` | `DELETE FROM users` — empty table returned |
| `length` | `SELECT COUNT(*) FROM users` |
| `.[] \| insert("name", age, "role")` | `INSERT INTO users VALUES ('name', age, 'role')` |
| `.[] \| update(.col, value, <pred>)` | `UPDATE users SET col = value WHERE <pred>` |

Predicates may combine leaf comparisons with `&&` (AND) or `||` (OR).
Operators: `==`, `!=`, `>`, `>=`, `<`, `<=`. String and role values must be
double-quoted in jq.

---

## Folder layout

```
QueryBridge/
├── ProofPilot/                         Lean 4 sources
│   ├── lakefile.toml                   package manifest (Lake v5)
│   ├── lean-toolchain                  pinned to leanprover/lean4:v4.29.0
│   ├── Main.lean                       JDB / SDB models, the JQuery/SQuery
│   │                                   languages, `query_equiv` theorem
│   ├── Error.lean                      Bug-seeded copy of Main.lean
│   │                                   (Plausible exercises the bugs)
│   ├── Properties.lean                 Arbitrary/Shrinkable + 4 props
│   ├── Test.lean                       editor-visible `#test` directives
│   ├── PropRunner.lean                 binary: Plausible.checkIO → JSON
│   ├── ProofTrace.lean                 binary: importModules + collectAxioms → JSON
│   ├── JqGenMain.lean                  jq string parser (lib only)
│   ├── SqlGenMain.lean                 binary: per-query verified path
│   ├── SqlGenError.lean                binary: per-query bug demo (legacy)
│   ├── SqlGenBug2.lean / SqlGenBug3.lean   ditto
│   └── Bug2.lean / Bug3.lean           bug-seeded variants used by the above
│
├── backend/                            FastAPI + LLM + Lean subprocess driver
│   ├── main.py                         routes: /api/query /api/properties /api/proofs
│   ├── translator.py                   Python jq→SQL (mirror of the Lean proof)
│   ├── executor.py                     run_jq + run_sql on the seed dataset
│   ├── lean_client.py                  spawns sqlGenMain
│   ├── llm_client.py                   nl_to_jq via Anthropic SDK or mock
│   ├── proof_witness.py                builds per-query proof witness
│   ├── counterexample_runner.py        spawns propRunner / proofTrace
│   ├── seed_data.py                    7 hardcoded users
│   └── requirements.txt
│
├── frontend/                           Vite + React + TypeScript
│   └── src/
│       ├── App.tsx                     Query / Proofs / Property-tests tabs
│       ├── api.ts                      typed fetch wrappers
│       ├── types.ts                    response shape declarations
│       └── components/
│           ├── QueryInput.tsx
│           ├── Pipeline.tsx
│           ├── SplitResults.tsx
│           ├── ProofWitnessPanel.tsx   per-query witness (under /api/query)
│           ├── PropertyResults.tsx     /api/properties tab
│           ├── ProofResults.tsx        /api/proofs tab
│           └── DatabaseViewer.tsx
│
├── figures/                            screenshots referenced in this README
├── formalization.{tex,pdf}             companion writeup of the Lean proof
├── setup.sh                            one-shot installer (backend + frontend)
└── Dockerfile                          multi-stage image, single-port serve
```

---

## Build & run

### Docker (one command)

```bash
docker build -t querybridge .
docker run --rm -p 8000:8000 querybridge
# open http://localhost:8000
```

The image is multi-stage: it builds the React bundle, fetches Mathlib's
prebuilt `.olean`s and compiles the Lean executables, then assembles a slim
Python runtime that serves the API and the SPA on a single port. Pass
`-e ANTHROPIC_API_KEY=…` to use the live LLM in place of the mock.

### Local — three steps

`setup.sh` automates the full flow (backend deps, backend up, frontend deps,
Vite up, browser launch):

```bash
./setup.sh
```

Or, manually:

#### Lean binaries (one-time, ~30 s on warm cache)

```bash
cd ProofPilot
lake update                # one-time Mathlib + Plausible fetch
lake build sqlGenMain sqlGenError sqlGenBug2 sqlGenBug3 propRunner proofTrace
```

Pass the explicit targets — a bare `lake build` will fail on `Test.lean`,
because Plausible *does* find counter-examples in `Error.lean` (that is the
intended demo, not a configuration error). If the binaries aren't built,
the rest of the app still works; the Lean-derived SQL box and the two
property/proof tabs degrade gracefully and prompt you to build.

#### Backend

```bash
cd backend
pip install -r requirements.txt
uvicorn main:app --port 8000 --reload
```

#### Frontend (separate terminal)

```bash
cd frontend
npm install
npm run dev
# → http://localhost:5173
```

The UI's **Mock LLM** toggle is on by default — no API key needed. To use
the live model, copy `backend/.env.example` to `backend/.env` and set
`ANTHROPIC_API_KEY`.

---

## Origin

Built during the **LeanLang for Verified Autonomy Hackathon**
(April 17–18 + online through May 1, 2026) at the
**Indian Institute of Science (IISc), Bangalore**.
Sponsored by **[Emergence AI](https://www.emergence.ai)**.
Organized by **[Emergence India Labs](https://east.emergence.ai)** in
collaboration with **IISc Bangalore**.

## Acknowledgments

- **Emergence AI** — Hackathon sponsor
- **Emergence India Labs** — Event organizer and research direction
- **Indian Institute of Science (IISc), Bangalore** — Academic partner,
  hackathon co-design, tutorials, and mentorship

## Links

- [Hackathon Page](https://east.emergence.ai/hackathon-april2026.html)
- [Emergence India Labs](https://east.emergence.ai)
- [Emergence AI](https://www.emergence.ai)
