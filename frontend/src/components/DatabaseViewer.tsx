import { useEffect, useState } from 'react'

type User = Record<string, unknown>

export default function DatabaseViewer() {
  const [open, setOpen] = useState(false)
  const [users, setUsers] = useState<User[] | null>(null)
  const [error, setError] = useState<string | null>(null)

  useEffect(() => {
    if (!open || users) return
    fetch('/api/data')
      .then(r => r.ok ? r.json() : Promise.reject(r))
      .then((d: { users: User[] }) => setUsers(d.users))
      .catch(() => setError('Failed to fetch seed database.'))
  }, [open, users])

  const cols = users && users.length > 0 ? Object.keys(users[0]) : []

  return (
    <>
      <button className="db-viewer-btn" onClick={() => setOpen(true)}>
        View seed database
      </button>
      {open && (
        <div className="db-viewer-overlay" onClick={() => setOpen(false)}>
          <div className="db-viewer-modal" onClick={e => e.stopPropagation()}>
            <div className="db-viewer-header">
              <span className="db-viewer-title">Seed database</span>
              <button className="db-viewer-close" onClick={() => setOpen(false)}>×</button>
            </div>
            <div className="db-viewer-body">
              {error ? (
                <div className="empty-state">{error}</div>
              ) : !users ? (
                <div className="empty-state">Loading…</div>
              ) : (
                <table className="result-table">
                  <thead>
                    <tr>{cols.map(c => <th key={c}>{c}</th>)}</tr>
                  </thead>
                  <tbody>
                    {users.map((u, i) => (
                      <tr key={i}>
                        {cols.map(c => <td key={c}>{String(u[c] ?? '')}</td>)}
                      </tr>
                    ))}
                  </tbody>
                </table>
              )}
            </div>
          </div>
        </div>
      )}
    </>
  )
}
