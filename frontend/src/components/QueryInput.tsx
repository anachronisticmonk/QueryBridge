const EXAMPLES = [
  'show me everyone',
  'find users older than 30',
  'get names of users under 25',
  'find Alice',
  'delete users younger than 25',
  'how many users',
]

interface Props {
  value: string
  onChange: (v: string) => void
  onRun: (v: string) => void
  loading: boolean
  useMock: boolean
  onToggleMock: () => void
  useError: boolean
  onToggleError: () => void
}

export default function QueryInput({ value, onChange, onRun, loading, useMock, onToggleMock, useError, onToggleError }: Props) {
  function handleKey(e: React.KeyboardEvent) {
    if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) {
      onRun(value)
    }
  }

  return (
    <div className="query-input">
      <textarea
        className="query-textarea"
        placeholder="Ask in plain English, e.g. 'find all users older than 30'…"
        value={value}
        onChange={e => onChange(e.target.value)}
        onKeyDown={handleKey}
        rows={2}
        autoFocus
      />
      <div className="examples">
        {EXAMPLES.map(ex => (
          <button key={ex} className="example-btn" onClick={() => onRun(ex)}>
            {ex}
          </button>
        ))}
      </div>
      <div className="query-controls">
        <div className="toggle-group">
          <label className="mock-toggle">
            <input type="checkbox" checked={useMock} onChange={onToggleMock} />
            Mock LLM (no API key needed)
          </label>
          <label className="bug-toggle" title="Run the buggy variant Error.lean instead of Main.lean — counter-example surfaces on count queries.">
            <input type="checkbox" checked={useError} onChange={onToggleError} />
            Use buggy variant (Error.lean)
          </label>
        </div>
        <button
          className="run-btn"
          onClick={() => onRun(value)}
          disabled={loading || !value.trim()}
        >
          {loading ? 'Running…' : 'Run Query ▶'}
        </button>
      </div>
    </div>
  )
}
