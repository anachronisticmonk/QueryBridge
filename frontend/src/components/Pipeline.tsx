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

  const buggy = result?.lean_used_error === true
  const leanArrowClass = `pipeline-arrow lean${buggy ? ' error' : ''}`

  return (
    <div className="pipeline">
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

      {/* Arrow: Python translator (unverified mirror) */}
      <div className="pipeline-arrow translator">
        <span className="arrow-label">Python translator</span>
        <span className="arrow-line" />
      </div>

      {/* Box 3 — Python translator's SQL */}
      <div className="pipeline-box sql">
        <span className="box-label">SQL (translator.py)</span>
        {loading && !result ? (
          <span className="box-content placeholder loading">translating…</span>
        ) : result ? (
          <span className="box-content">{result.sql}</span>
        ) : (
          <span className="box-content placeholder">—</span>
        )}
      </div>

      {/* Arrow: Lean-derived (the verified path) */}
      <div className={leanArrowClass}>
        <span className="arrow-label">Lean 4</span>
        <span className="arrow-line" />
        {buggy ? (
          <span className="warning-badge">⚠ Buggy variant</span>
        ) : (
          <span className="verified-badge">✓ Proven</span>
        )}
      </div>

      {/* Box 4 — Lean-derived SQL */}
      <div className="pipeline-box lean-sql">
        <span className="box-label">SQL (Lean-derived)</span>
        {loading && !result ? (
          <span className="box-content placeholder loading">deriving…</span>
        ) : result?.lean_sql ? (
          <span className="box-content">{result.lean_sql}</span>
        ) : result ? (
          <span className="box-content placeholder">
            Lean exe not built — run <code>lake build sqlGenMain sqlGenError</code>
          </span>
        ) : (
          <span className="box-content placeholder">—</span>
        )}
      </div>
    </div>
  )
}
