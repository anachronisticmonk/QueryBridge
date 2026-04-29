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
  const showLeanBox = !!result?.lean_sql || (loading && !result)
  const leanArrowClass = `pipeline-arrow lean${buggy ? ' error' : ''}`

  return (
    <div className={`pipeline${showLeanBox ? '' : ' compact'}`}>
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

      {/* Box 3 — SQL */}
      <div className="pipeline-box sql">
        <span className="box-label">SQL</span>
        {loading && !result ? (
          <span className="box-content placeholder loading">translating…</span>
        ) : result ? (
          <span className="box-content">{result.sql}</span>
        ) : (
          <span className="box-content placeholder">—</span>
        )}
      </div>

      {showLeanBox && (
        <>
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
            ) : (
              <span className="box-content">{result?.lean_sql}</span>
            )}
          </div>
        </>
      )}
    </div>
  )
}
