import { useEffect, useState } from 'react'

type Row = Record<string, unknown>

interface CounterExample {
  name: string
  title: string
  bug: string
  explanation: string
  jq: string
  jdb: Row[]
  available: boolean
  matched?: boolean
  missing_binary?: string
  jq_result?: unknown
  sq_result?: unknown
  sql?: string
}

function ResultPanel({ label, payload }: { label: string; payload: unknown }) {
  // Two cases: payload is an array of rows or an object with `count`.
  if (Array.isArray(payload) && payload.length > 0 && typeof payload[0] === 'object') {
    const rows = payload as Row[]
    const cols = Object.keys(rows[0])
    return (
      <div className="ce-result">
        <div className="ce-result-label">{label}</div>
        <table className="result-table">
          <thead><tr>{cols.map(c => <th key={c}>{c}</th>)}</tr></thead>
          <tbody>
            {rows.map((row, i) => (
              <tr key={i}>{cols.map(c => <td key={c}>{String(row[c] ?? '')}</td>)}</tr>
            ))}
          </tbody>
        </table>
      </div>
    )
  }
  // scalar / count
  return (
    <div className="ce-result">
      <div className="ce-result-label">{label}</div>
      <pre className="ce-scalar">{JSON.stringify(payload, null, 2)}</pre>
    </div>
  )
}

export default function CounterExampleGallery() {
  const [items, setItems] = useState<CounterExample[] | null>(null)
  const [error, setError] = useState<string | null>(null)

  useEffect(() => {
    fetch('/api/counterexamples')
      .then(r => r.ok ? r.json() : Promise.reject(r))
      .then((d: { items: CounterExample[] }) => setItems(d.items))
      .catch(() => setError('Failed to fetch counter-examples.'))
  }, [])

  if (error) return <div className="pipeline-error">{error}</div>
  if (!items) return <div className="empty-state">Loading counter-examples…</div>

  return (
    <div className="ce-gallery">
      <div className="ce-gallery-header">
        <h2>Plausible-style counter-examples</h2>
        <p className="ce-gallery-sub">
          Each card below is a buggy variant of <code>eval_jquery</code> in Lean. The
          input database, the buggy jq result, and the correct SQL result are shown
          side-by-side. Property-based testing in <code>Test.lean</code> would discover
          divergences like these as failing instances of <code>prop_translation_correct</code>.
        </p>
      </div>

      {items.map(it => (
        <div key={it.name} className="ce-card">
          <div className="ce-card-header">
            <div>
              <span className="ce-card-title">{it.title}</span>
              <code className="ce-bug-meta">{it.bug}</code>
            </div>
            {it.available && it.matched === false && <span className="ce-card-badge fail">✗ Property fails</span>}
            {it.available && it.matched === true && <span className="ce-card-badge ok">⊘ Bug not triggered by this input</span>}
            {!it.available && (
              <span className="ce-card-badge missing">
                Binary missing: <code>{it.missing_binary}</code>
              </span>
            )}
          </div>

          <div className="ce-card-body">
            <p className="ce-explanation">{it.explanation}</p>

            <div className="ce-section">
              <span className="ce-section-label">Input JSON database</span>
              <pre className="ce-scalar">{JSON.stringify(it.jdb, null, 2)}</pre>
            </div>

            <div className="ce-section">
              <span className="ce-section-label">jq query</span>
              <code className="ce-jq">{it.jq}</code>
              {it.sql && (
                <code className="ce-jq" style={{ marginTop: '0.3rem' }}>{it.sql}</code>
              )}
            </div>

            {it.matched === false && (
              <div className="ce-results-grid">
                <ResultPanel label="eval_jquery (buggy)" payload={it.jq_result} />
                <ResultPanel label="eval_squery (correct)" payload={it.sq_result} />
              </div>
            )}
          </div>
        </div>
      ))}
    </div>
  )
}
