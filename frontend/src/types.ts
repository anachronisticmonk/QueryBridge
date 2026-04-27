export interface Counterexample {
  jq_result: unknown
  sql_result: unknown
  explanation: string
}

export interface QueryResponse {
  jq: string
  sql: string
  sql_raw: string
  query_type: 'find' | 'delete' | 'count'
  jq_results: (Record<string, unknown> | string | number)[]
  sql_results: Record<string, unknown>[]
  sql_columns: string[]
  verified: boolean
  lean_sql: string | null
  lean_used_error: boolean
  counterexample: Counterexample | null
}

export interface AppState {
  naturalLanguage: string
  useMock: boolean
  useError: boolean
  loading: boolean
  result: QueryResponse | null
  error: string | null
}
