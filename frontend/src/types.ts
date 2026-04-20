export interface QueryResponse {
  jq: string
  sql: string
  sql_raw: string
  query_type: 'find' | 'delete'
  jq_results: (Record<string, unknown> | string | number)[]
  sql_results: Record<string, unknown>[]
  sql_columns: string[]
  verified: boolean
}

export interface AppState {
  naturalLanguage: string
  useMock: boolean
  loading: boolean
  result: QueryResponse | null
  error: string | null
}
