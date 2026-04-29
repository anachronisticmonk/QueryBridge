import { useState } from 'react'
import type { QueryResponse } from './types'
import { runQuery } from './api'
import QueryInput from './components/QueryInput'
import Pipeline from './components/Pipeline'
import SplitResults from './components/SplitResults'
import DatabaseViewer from './components/DatabaseViewer'
import CounterExampleGallery from './components/CounterExampleGallery'

export default function App() {
  const [nl, setNl] = useState('')
  const [useMock, setUseMock] = useState(true)
  const [useError, setUseError] = useState(false)
  const [loading, setLoading] = useState(false)
  const [result, setResult] = useState<QueryResponse | null>(null)
  const [error, setError] = useState<string | null>(null)
  const [view, setView] = useState<'query' | 'gallery'>('query')

  async function handleRun(query: string) {
    if (!query.trim()) return
    setNl(query)
    setLoading(true)
    setError(null)
    setResult(null)
    try {
      const r = await runQuery(query, useMock, useError)
      setResult(r)
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setLoading(false)
    }
  }

  return (
    <div className="app">
      <header className="app-header">
        <div className="header-logo">
          <span className="logo-diamond">◆</span>
          <h1>QueryBridge</h1>
        </div>
        <p className="tagline">
          Formally verified jq → SQL translation
        </p>
        <div className="header-actions">
          <DatabaseViewer />
          <div className="view-switch" role="tablist">
            <button
              className={`view-tab${view === 'query' ? ' active' : ''}`}
              onClick={() => setView('query')}
            >
              Query
            </button>
            <button
              className={`view-tab${view === 'gallery' ? ' active' : ''}`}
              onClick={() => setView('gallery')}
            >
              Counter-examples
            </button>
          </div>
        </div>
      </header>

      <main className="app-main">
        {view === 'gallery' ? (
          <CounterExampleGallery />
        ) : (
        <>
        <section className="section-query">
          <QueryInput
            value={nl}
            onChange={setNl}
            onRun={handleRun}
            loading={loading}
            useMock={useMock}
            onToggleMock={() => setUseMock(v => !v)}
            useError={useError}
            onToggleError={() => setUseError(v => !v)}
          />
        </section>

        {(loading || result || error) && (
          <section className="section-pipeline">
            <Pipeline nl={nl} result={result} loading={loading} error={error} />
          </section>
        )}

        {result && (
          <section className="section-results">
            <SplitResults result={result} />
          </section>
        )}

        <section className="section-proof-teaser">
          <details>
            <summary>
              <span className="proof-badge">∀</span>
              Formal Verification — Lean 4
            </summary>
            <div className="proof-content">
              <p>
                The translation from jq to SQL is backed by theorem{' '}
                <code>query_equiv</code> in <code>ProofPilot/Main.lean</code>.
              </p>
              <p>
                The theorem proves: given two databases holding the same data
                (one as JSON, one as SQL rows), for every result{' '}
                <code>res</code>, <code>res ∈ eval_jquery jd jq ↔ res ∈
                eval_squery sd (jqueryToSquery jq)</code>.
              </p>
              <p className="proof-note">
                Proof display coming soon.
              </p>
            </div>
          </details>
        </section>
        </>
        )}
      </main>
    </div>
  )
}
