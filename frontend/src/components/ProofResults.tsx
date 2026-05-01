import { useEffect, useState } from 'react'
import type { ProofResponse, ProofTrace } from '../types'
import { fetchProofs } from '../api'

const FOUNDATIONAL = new Set(['propext', 'Quot.sound', 'Classical.choice'])

const STATUS_LABEL: Record<ProofTrace['status'], string> = {
  verified: '✓ Kernel-checked',
  sorry:    '✗ Contains sorry',
  missing:  '? Not in environment',
}

function StatusBadge({ status }: { status: ProofTrace['status'] }) {
  return (
    <span className={`proof-badge proof-badge-${status}`}>{STATUS_LABEL[status]}</span>
  )
}

function AxiomList({ axioms }: { axioms: string[] }) {
  if (axioms.length === 0) {
    return <span className="proof-axiom-empty">none — proven from definitional equality alone</span>
  }
  return (
    <ul className="proof-axiom-list">
      {axioms.map(a => (
        <li key={a} className={`proof-axiom${FOUNDATIONAL.has(a) ? ' foundational' : ''}`}>
          <code>{a}</code>
          {FOUNDATIONAL.has(a) && <span className="proof-axiom-tag">Lean foundational</span>}
        </li>
      ))}
    </ul>
  )
}

function ProofCard({ item }: { item: ProofTrace }) {
  const sorryHit = item.axioms?.includes('sorryAx') ?? false
  return (
    <article className={`proof-card proof-card-${item.status}`}>
      <header className="proof-card-head">
        <div>
          <h3 className="proof-card-title">{item.title}</h3>
          <code className="proof-card-name">{item.name}</code>
        </div>
        <StatusBadge status={item.status} />
      </header>

      <p className="proof-description">{item.description}</p>

      {item.type && (
        <div className="proof-section">
          <span className="proof-section-label">Statement (Lean kernel form)</span>
          <pre className="proof-source">{item.type}</pre>
        </div>
      )}

      <div className="proof-section">
        <span className="proof-section-label">
          Axiom dependencies — collected by{' '}
          <code>Lean.collectAxioms</code>
        </span>
        <AxiomList axioms={item.axioms ?? []} />
        {sorryHit && (
          <div className="proof-sorry-warning">
            ⚠ <code>sorryAx</code> is in the axiom set — this proof is incomplete.
          </div>
        )}
      </div>

      {item.proofTermDepth !== undefined && (
        <div className="proof-meta">
          Proof-term depth (kernel): <code>{item.proofTermDepth}</code>
          {item.kind && <> · kind: <code>{item.kind}</code></>}
        </div>
      )}
    </article>
  )
}

export default function ProofResults() {
  const [data, setData] = useState<ProofResponse | null>(null)
  const [error, setError] = useState<string | null>(null)
  const [loading, setLoading] = useState(true)

  useEffect(() => {
    let cancelled = false
    setLoading(true)
    fetchProofs()
      .then(d => { if (!cancelled) { setData(d); setLoading(false) } })
      .catch(e => { if (!cancelled) { setError(e.message); setLoading(false) } })
    return () => { cancelled = true }
  }, [])

  if (loading) return (
    <div className="prop-results-loading">
      Loading <code>Main.olean</code> into a Lean kernel and walking
      proof terms with <code>Lean.collectAxioms</code>… (~5 s on first run.)
    </div>
  )

  if (error) return <div className="pipeline-error">{error}</div>
  if (!data) return null

  if (!data.available) {
    return (
      <div className="prop-results-unavailable">
        <p>
          The Lean proof-trace binary is not available
          {data.missing_binary ? <> — looking for <code>{data.missing_binary}</code></> : null}.
        </p>
        <pre className="prop-results-build">
{`cd ProofPilot
lake build proofTrace`}
        </pre>
        {data.error && <p className="prop-results-err">{data.error}</p>}
      </div>
    )
  }

  const verified = data.items.filter(i => i.status === 'verified').length
  const incomplete = data.items.filter(i => i.status !== 'verified').length

  return (
    <div className="proof-results">
      <header className="prop-results-header">
        <div>
          <h2>Verified theorems — kernel-checked proof objects</h2>
          <p className="prop-results-sub">
            The Python backend invokes the <code>proofTrace</code> Lean binary,
            which uses <code>Lean.importModules</code> to load{' '}
            <code>Main.lean</code>'s kernel-checked environment, then for each
            theorem walks its proof term with <code>Lean.collectAxioms</code> and
            pretty-prints the statement via <code>Meta.ppExpr</code>. The cards
            below are what the Lean kernel actually accepted; a theorem is
            marked <strong>verified</strong> iff <code>sorryAx</code> is{' '}
            <em>not</em> in its transitive axiom set.
          </p>
        </div>
        <div className="prop-results-summary">
          <div><span className="prop-results-num">{verified}</span><span className="prop-results-num-label">verified</span></div>
          {incomplete > 0 && <div><span className="prop-results-num">{incomplete}</span><span className="prop-results-num-label">incomplete</span></div>}
        </div>
      </header>

      {data.items.map(it => <ProofCard key={it.name} item={it} />)}
    </div>
  )
}
