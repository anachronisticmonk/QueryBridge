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

      {/* Arrow: Lean verified */}
      <div className="pipeline-arrow lean">
        <span className="arrow-label">Lean 4</span>
        <span className="arrow-line" />
        <span className="verified-badge">✓ Proven</span>
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
    </div>
  )
}
