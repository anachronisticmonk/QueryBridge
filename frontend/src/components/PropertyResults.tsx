import { useEffect, useState } from 'react'
import type { PropertyResponse, PropertyResult } from '../types'
import { fetchProperties } from '../api'

const STATUS_LABEL: Record<PropertyResult['status'], string> = {
  success:  '✓ No counter-example found',
  gaveUp:   '⊘ Plausible gave up',
  failure:  '✗ Counter-example found',
}

function StatusBadge({ status }: { status: PropertyResult['status'] }) {
  return (
    <span className={`prop-badge prop-badge-${status}`}>{STATUS_LABEL[status]}</span>
  )
}

function CounterExample({ values, shrinks }: { values: string[]; shrinks: number }) {
  return (
    <div className="prop-counter">
      <div className="prop-counter-head">
        <span className="prop-section-label">Counter-example from Plausible</span>
        <span className="prop-shrinks">shrunk in {shrinks} step{shrinks === 1 ? '' : 's'}</span>
      </div>
      <pre className="prop-counter-pre">{values.join('\n')}</pre>
    </div>
  )
}

function PropertyCard({ item }: { item: PropertyResult }) {
  return (
    <article className={`prop-card prop-card-${item.status}`}>
      <header className="prop-card-head">
        <h3 className="prop-card-title">{item.title}</h3>
        <StatusBadge status={item.status} />
      </header>

      <p className="prop-description">{item.description}</p>

      <div className="prop-section">
        <span className="prop-section-label">Property (as written in Lean)</span>
        <pre className="prop-source">{`#test ${item.prop}`}</pre>
      </div>

      <div className="prop-section">
        <span className="prop-section-label">Bug seeded in Error.lean</span>
        <code className="prop-bug">{item.bug}</code>
      </div>

      {item.status === 'failure' && item.counterExample && (
        <CounterExample
          values={item.counterExample}
          shrinks={item.shrinks ?? 0}
        />
      )}

      {item.status === 'gaveUp' && item.gaveUpAfter !== undefined && (
        <div className="prop-gaveup">
          Plausible gave up after {item.gaveUpAfter} attempts that failed
          to satisfy the property's preconditions.
        </div>
      )}
    </article>
  )
}

export default function PropertyResults() {
  const [data, setData] = useState<PropertyResponse | null>(null)
  const [error, setError] = useState<string | null>(null)
  const [loading, setLoading] = useState(true)

  useEffect(() => {
    let cancelled = false
    setLoading(true)
    fetchProperties()
      .then(d => { if (!cancelled) { setData(d); setLoading(false) } })
      .catch(e => { if (!cancelled) { setError(e.message); setLoading(false) } })
    return () => { cancelled = true }
  }, [])

  if (loading) return (
    <div className="prop-results-loading">
      Running Plausible in Lean… (this calls the <code>propRunner</code> binary
      and can take a few seconds on first run.)
    </div>
  )

  if (error) return (
    <div className="pipeline-error">{error}</div>
  )

  if (!data) return null

  if (!data.available) {
    return (
      <div className="prop-results-unavailable">
        <p>
          The Plausible runner binary is not available
          {data.missing_binary ? <> — looking for <code>{data.missing_binary}</code></> : null}.
        </p>
        <pre className="prop-results-build">
{`cd ProofPilot
lake build propRunner`}
        </pre>
        {data.error && <p className="prop-results-err">{data.error}</p>}
      </div>
    )
  }

  const failures = data.items.filter(i => i.status === 'failure').length
  const successes = data.items.filter(i => i.status === 'success').length
  const gaveUps = data.items.filter(i => i.status === 'gaveUp').length

  return (
    <div className="prop-results">
      <header className="prop-results-header">
        <div>
          <h2>Property-based testing — driven from Lean</h2>
          <p className="prop-results-sub">
            The Python backend invokes the <code>propRunner</code> Lean binary,
            which calls <code>Plausible.Testable.checkIO</code> on each property
            and returns a structured <code>TestResult</code>. The card below
            shows what came back — the proof object the Lean side handed us.
            Properties are checked against the deliberately-buggy{' '}
            <code>eval_jquery</code> in <code>ProofPilot/Error.lean</code>;
            failing checks below mean Plausible found a concrete database +
            query that violates the property.
          </p>
        </div>
        <div className="prop-results-summary">
          <div><span className="prop-results-num">{failures}</span><span className="prop-results-num-label">failed</span></div>
          <div><span className="prop-results-num">{successes}</span><span className="prop-results-num-label">passed</span></div>
          {gaveUps > 0 && <div><span className="prop-results-num">{gaveUps}</span><span className="prop-results-num-label">gave up</span></div>}
        </div>
      </header>

      {data.items.map(it => <PropertyCard key={it.id} item={it} />)}
    </div>
  )
}
