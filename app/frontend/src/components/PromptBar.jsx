import { useState } from 'react';

export default function PromptBar({ onRun, loading, examples }) {
  const [query, setQuery] = useState('');

  function handleSubmit(e) {
    e.preventDefault();
    if (query.trim()) onRun(query.trim());
  }

  return (
    <div className="prompt-bar">
      <form onSubmit={handleSubmit} className="prompt-form">
        <input
          className="prompt-input"
          type="text"
          placeholder="e.g. names of all users under the age of 10"
          value={query}
          onChange={e => setQuery(e.target.value)}
          disabled={loading}
        />
        <button className="run-btn" type="submit" disabled={loading || !query.trim()}>
          {loading ? 'Running…' : 'Run'}
        </button>
      </form>

      <div className="examples">
        {examples.map(ex => (
          <button
            key={ex}
            className="example-chip"
            onClick={() => { setQuery(ex); onRun(ex); }}
            disabled={loading}
          >
            {ex}
          </button>
        ))}
      </div>
    </div>
  );
}
