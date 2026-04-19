import { useState } from 'react';
import PromptBar         from './components/PromptBar.jsx';
import QueryPane         from './components/QueryPane.jsx';
import VerificationWidget from './components/VerificationWidget.jsx';

const EXAMPLES = [
  'names of all users under the age of 10',
  'email addresses of users older than 20',
  'all users sorted by age',
];

export default function App() {
  const [loading,      setLoading]      = useState(false);
  const [result,       setResult]       = useState(null);
  const [error,        setError]        = useState(null);

  async function handleRun(query) {
    setLoading(true);
    setError(null);
    setResult(null);
    try {
      const res  = await fetch('/api/run', {
        method:  'POST',
        headers: { 'Content-Type': 'application/json' },
        body:    JSON.stringify({ query }),
      });
      const data = await res.json();
      if (!res.ok) throw new Error(data.error || 'Server error');
      setResult(data);
    } catch (e) {
      setError(e.message);
    } finally {
      setLoading(false);
    }
  }

  return (
    <div className="app">
      <header className="app-header">
        <span className="logo">QueryBridge</span>
        <span className="tagline">NL → jq + SQL, verified by Lean</span>
      </header>

      <PromptBar onRun={handleRun} loading={loading} examples={EXAMPLES} />

      {error && <div className="error-banner">⚠ {error}</div>}

      {result && (
        <>
          <div className="split-view">
            <QueryPane
              lang="jq"
              query={result.jq}
              execution={result.jqResult}
            />
            <div className="divider" />
            <QueryPane
              lang="sql"
              query={result.sql}
              execution={result.sqlResult}
            />
          </div>

          <VerificationWidget verification={result.verification} jquery={result.jquery} />
        </>
      )}

      {!result && !loading && (
        <div className="empty-state">
          Enter a natural-language query above and press Run.
        </div>
      )}
    </div>
  );
}
