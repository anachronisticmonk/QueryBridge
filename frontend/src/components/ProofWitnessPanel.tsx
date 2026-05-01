import type { ProofWitness } from '../types'

const FOUNDATIONAL = new Set(['propext', 'Quot.sound', 'Classical.choice'])

interface Props {
  witness: ProofWitness | null
}

export default function ProofWitnessPanel({ witness }: Props) {
  if (!witness || !witness.available) return null

  const matchOk = witness.kernel_match === true
  const matchClass = matchOk ? 'pw-match-ok' : 'pw-match-fail'

  return (
    <section className="proof-witness">
      <header className="pw-head">
        <div>
          <span className="pw-eyebrow">Per-query proof witness</span>
          <h3 className="pw-title">
            <code>{witness.theorem ?? 'query_equiv'}</code> ·{' '}
            <code>{witness.case_translation}</code>
          </h3>
        </div>
        <span className={`pw-match-badge ${matchClass}`}>
          {matchOk
            ? '✓ Lean kernel reduced both sides to equivalent values'
            : '✗ Kernel match failed'}
        </span>
      </header>

      {witness.theorem_statement && (
        <div className="pw-section">
          <span className="pw-section-label">Universal theorem (Main.lean)</span>
          <pre className="pw-source">{witness.theorem_statement}</pre>
        </div>
      )}

      {witness.case_gloss && (
        <p className="pw-gloss">{witness.case_gloss}</p>
      )}

      {witness.case_source && (
        <div className="pw-section">
          <span className="pw-section-label">
            Proof case for this query — Main.lean
            {witness.case_source_lines && (
              <code className="pw-source-loc">
                :{witness.case_source_lines[0]}–{witness.case_source_lines[1]}
              </code>
            )}
          </span>
          <pre className="pw-source pw-proof-source">{witness.case_source}</pre>
        </div>
      )}

      {witness.case_supporting_lemmas && witness.case_supporting_lemmas.length > 0 && (
        <div className="pw-section">
          <span className="pw-section-label">Supporting lemmas this case uses</span>
          <ul className="pw-lemma-list">
            {witness.case_supporting_lemmas.map(l => (
              <li key={l} className="pw-lemma"><code>{l}</code></li>
            ))}
          </ul>
        </div>
      )}

      <div className="pw-footer">
        <div className="pw-footer-block">
          <span className="pw-section-label">Axiom dependencies</span>
          <div className="pw-axiom-row">
            {(witness.axioms ?? []).length === 0 && (
              <span className="pw-axiom-empty">none</span>
            )}
            {(witness.axioms ?? []).map(a => (
              <span
                key={a}
                className={`pw-axiom${FOUNDATIONAL.has(a) ? ' foundational' : ''}`}
              >
                <code>{a}</code>
              </span>
            ))}
          </div>
        </div>
        {witness.proofTermDepth !== undefined && witness.proofTermDepth !== null && (
          <div className="pw-footer-block">
            <span className="pw-section-label">Proof-term depth (kernel)</span>
            <code className="pw-metric">{witness.proofTermDepth}</code>
          </div>
        )}
      </div>
    </section>
  )
}
