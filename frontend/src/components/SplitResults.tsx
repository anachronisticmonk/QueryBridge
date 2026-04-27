import type { QueryResponse } from '../types'

interface Props {
  result: QueryResponse
}

type Row = Record<string, unknown>

function normaliseJqResults(
  raw: QueryResponse['jq_results'],
  col: string | null,
): { cols: string[]; rows: Row[] } {
  if (raw.length === 0) return { cols: [], rows: [] }

  if (col) {
    return {
      cols: [col],
      rows: raw.map(v => ({ [col]: v })),
    }
  }

  if (typeof raw[0] === 'object' && raw[0] !== null) {
    const cols = Object.keys(raw[0] as Row)
    return { cols, rows: raw as Row[] }
  }

  return { cols: ['value'], rows: raw.map(v => ({ value: v })) }
}

function ResultTable({ cols, rows }: { cols: string[]; rows: Row[] }) {
  if (rows.length === 0) {
    return <div className="empty-state">No results</div>
  }
  return (
    <table className="result-table">
      <thead>
        <tr>{cols.map(c => <th key={c}>{c}</th>)}</tr>
      </thead>
      <tbody>
        {rows.map((row, i) => (
          <tr key={i}>
            {cols.map(c => <td key={c}>{String(row[c] ?? '')}</td>)}
          </tr>
        ))}
      </tbody>
    </table>
  )
}

export default function SplitResults({ result }: Props) {
  const isDelete = result.query_type === 'delete'
  const colName = result.jq.includes('| .') ? result.jq.split('| .').pop()?.trim() ?? null : null

  const jqNorm = normaliseJqResults(result.jq_results, colName ?? null)
  const sqlCols = result.sql_columns
  const sqlRows = result.sql_results

  const subtitle = isDelete ? 'Remaining rows after DELETE' : `${result.jq_results.length} row(s)`
  const ce = result.counterexample

  return (
    <div className="split-results">
      {ce && (
        <div className="counterexample-alert">
          <div className="ce-header">✗ Counter-example: equivalence violated</div>
          <div className="ce-body">
            <div>
              <span className="ce-label">eval_jquery (buggy):</span>{' '}
              <code>{JSON.stringify(ce.jq_result)}</code>
            </div>
            <div>
              <span className="ce-label">eval_squery (correct):</span>{' '}
              <code>{JSON.stringify(ce.sql_result)}</code>
            </div>
            <div className="ce-explanation">{ce.explanation}</div>
          </div>
        </div>
      )}

      <div className="results-header">
        <span style={{ fontSize: '0.8rem', color: 'var(--muted)' }}>
          Running both queries on identical data…
        </span>
        {ce ? (
          <span className="results-match-badge failed">✗ Equivalence broken</span>
        ) : (
          <span className="results-match-badge">✓ Machine-verified equivalence</span>
        )}
      </div>

      <div className="results-panels">
        {/* Left — jq */}
        <div className="result-panel jq-panel">
          <div className="panel-header">
            <span className="panel-badge">jq</span>
            <span className="panel-subtitle">{subtitle}</span>
          </div>
          <div className="panel-body">
            <ResultTable cols={jqNorm.cols} rows={jqNorm.rows} />
          </div>
        </div>

        {/* Right — SQL */}
        <div className="result-panel sql-panel">
          <div className="panel-header">
            <span className="panel-badge">SQL</span>
            <span className="panel-subtitle">{subtitle}</span>
          </div>
          <div className="panel-body">
            <ResultTable cols={sqlCols} rows={sqlRows} />
          </div>
        </div>
      </div>
    </div>
  )
}
