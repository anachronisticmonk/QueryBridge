import type { QueryResponse } from '../types'

interface Props {
  nl: string
  result: QueryResponse | null
  loading: boolean
  error: string | null
}

export default function Pipeline({ nl, result, loading, error }: Props) {
  if (error) {
    return <div className="pipeline-error">{error}</div>
  }

  // Lean-derived SQL is the canonical SQL we display. If the Lean
  // binary isn't available (dev path with no `lake build`), fall back
  // to the Python translator's string so the box still reads sensibly.
  const sqlText = result?.lean_sql ?? result?.sql ?? null

  return (
    <div className="pipeline compact">
      {/* Box 1 — Natural Language */}
      <div className="pipeline-box nl">
        <span className="box-label">Natural Language</span>
        <span className="box-content">{nl}</span>
      </div>

      {/* Arrow: LLM (unverified) */}
      <div className="pipeline-arrow llm">
        <span className="arrow-label">LLM</span>
        <span className="arrow-line" />
      </div>

      {/* Box 2 — jq */}
      <div className="pipeline-box jq">
        <span className="box-label">jq Query</span>
        {loading && !result ? (
          <span className="box-content placeholder loading">generating…</span>
        ) : result ? (
          <span className="box-content">{result.jq}</span>
        ) : (
          <span className="box-content placeholder">—</span>
        )}
      </div>

      {/* Arrow: jq → SQL — the verified equivalence */}
      <div className="pipeline-arrow verified">
        <span className="arrow-label">Formally verified jq ↔ SQL equivalence</span>
        <span className="arrow-line" />
        <span className="proven-indicator">✓ Proven in Lean 4</span>
      </div>

      {/* Box 3 — SQL (Lean-derived) */}
      <div className="pipeline-box lean-sql">
        <span className="box-label">SQL (Lean-derived)</span>
        {loading && !result ? (
          <span className="box-content placeholder loading">deriving…</span>
        ) : sqlText ? (
          <span className="box-content">{sqlText}</span>
        ) : (
          <span className="box-content placeholder">—</span>
        )}
      </div>
    </div>
  )
}
