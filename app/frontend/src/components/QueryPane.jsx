export default function QueryPane({ lang, query, execution }) {
  const label  = lang === 'jq' ? 'jq' : 'SQL';
  const badge  = lang === 'jq' ? 'jq-badge' : 'sql-badge';
  const rows   = execution?.result;
  const hasErr = !execution?.ok;

  return (
    <div className="query-pane">
      <div className="pane-header">
        <span className={`lang-badge ${badge}`}>{label}</span>
        <span className="pane-subtitle">
          {lang === 'jq' ? 'runs on JSON datastore' : 'runs on SQLite datastore'}
        </span>
      </div>

      <pre className="code-block">{query}</pre>

      <div className="results-label">Results</div>

      {hasErr ? (
        <div className="result-error">{execution?.error}</div>
      ) : (
        <div className="result-table-wrap">
          {Array.isArray(rows) && rows.length === 0 && (
            <div className="result-empty">No rows returned</div>
          )}
          {Array.isArray(rows) && rows.length > 0 && (
            typeof rows[0] === 'object' && rows[0] !== null
              ? <ObjectTable rows={rows} />
              : <ScalarList  items={rows} />
          )}
        </div>
      )}
    </div>
  );
}

function ObjectTable({ rows }) {
  const cols = Object.keys(rows[0]);
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
  );
}

function ScalarList({ items }) {
  return (
    <ul className="scalar-list">
      {items.map((v, i) => <li key={i}>{String(v)}</li>)}
    </ul>
  );
}
