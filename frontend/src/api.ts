import type { QueryResponse } from './types'

export async function runQuery(
  naturalLanguage: string,
  mock: boolean,
  useError: boolean,
): Promise<QueryResponse> {
  const res = await fetch('/api/query', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ natural_language: naturalLanguage, mock, use_error: useError }),
  })
  if (!res.ok) {
    const err = await res.json().catch(() => ({ detail: 'Unknown error' }))
    throw new Error(err.detail ?? 'Query failed')
  }
  return res.json()
}
