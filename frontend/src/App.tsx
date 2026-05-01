import { useState } from 'react'
import type { QueryResponse } from './types'
import { runQuery } from './api'
import QueryInput from './components/QueryInput'
import Pipeline from './components/Pipeline'
import SplitResults from './components/SplitResults'
import ProofWitnessPanel from './components/ProofWitnessPanel'
import DatabaseViewer from './components/DatabaseViewer'
import PropertyResults from './components/PropertyResults'
import ProofResults from './components/ProofResults'

export default function App() {
  const [nl, setNl] = useState('')
  const [useMock, setUseMock] = useState(true)
  const [loading, setLoading] = useState(false)
  const [result, setResult] = useState<QueryResponse | null>(null)
  const [error, setError] = useState<string | null>(null)
  const [view, setView] = useState<'query' | 'proofs' | 'properties'>('query')

  async function handleRun(query: string) {
    if (!query.trim()) return
    setNl(query)
    setLoading(true)
    setError(null)
    setResult(null)
    try {
      const r = await runQuery(query, useMock)
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
              className={`view-tab${view === 'proofs' ? ' active' : ''}`}
              onClick={() => setView('proofs')}
            >
              Proofs
            </button>
            <button
              className={`view-tab${view === 'properties' ? ' active' : ''}`}
              onClick={() => setView('properties')}
            >
              Property tests
            </button>
          </div>
        </div>
      </header>

      <main className="app-main">
        {view === 'properties' ? (
          <PropertyResults />
        ) : view === 'proofs' ? (
          <ProofResults />
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

        {result && result.proof_witness && (
          <section className="section-proof-witness">
            <ProofWitnessPanel witness={result.proof_witness} />
          </section>
        )}
        </>
        )}
      </main>
    </div>
  )
}
