import type { QueryResponse, PropertyResponse, ProofResponse } from './types'

export async function runQuery(
  naturalLanguage: string,
  mock: boolean,
): Promise<QueryResponse> {
  const res = await fetch('/api/query', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ natural_language: naturalLanguage, mock }),
  })
  if (!res.ok) {
    const err = await res.json().catch(() => ({ detail: 'Unknown error' }))
    throw new Error(err.detail ?? 'Query failed')
  }
  return res.json()
}

export async function fetchProperties(): Promise<PropertyResponse> {
  const res = await fetch('/api/properties')
  if (!res.ok) {
    const err = await res.json().catch(() => ({ detail: 'Unknown error' }))
    throw new Error(err.detail ?? 'Failed to fetch properties')
  }
  return res.json()
}

export async function fetchProofs(): Promise<ProofResponse> {
  const res = await fetch('/api/proofs')
  if (!res.ok) {
    const err = await res.json().catch(() => ({ detail: 'Unknown error' }))
    throw new Error(err.detail ?? 'Failed to fetch proofs')
  }
  return res.json()
}
