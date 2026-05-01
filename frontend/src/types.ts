export interface ProofWitness {
  available: boolean
  reason?: string
  theorem?: string
  theorem_statement?: string
  axioms?: string[]
  proofTermDepth?: number | null
  case?: 'find' | 'drop' | 'prepend' | 'clear' | 'length' | 'modify'
  case_translation?: string
  case_gloss?: string
  case_supporting_lemmas?: string[]
  case_source_lines?: [number, number]
  case_source?: string
  kernel_match?: boolean | null
  squery_case?: string
  kernel_jq_result?: unknown
  kernel_sq_result?: unknown
}

export interface QueryResponse {
  jq: string
  sql: string
  sql_raw: string
  query_type: 'find' | 'delete' | 'count' | 'insert' | 'update'
  jq_results: (Record<string, unknown> | string | number)[]
  sql_results: Record<string, unknown>[]
  sql_columns: string[]
  verified: boolean
  lean_sql: string | null
  proof_witness: ProofWitness | null
}

export interface AppState {
  naturalLanguage: string
  useMock: boolean
  loading: boolean
  result: QueryResponse | null
  error: string | null
}

// Property-test results emitted by the propRunner Lean binary
// (see ProofPilot/PropRunner.lean and backend/counterexample_runner.py).
export type PropertyStatus = 'success' | 'gaveUp' | 'failure'

export interface PropertyResult {
  id: string
  title: string
  prop: string
  description: string
  bug: string
  status: PropertyStatus
  counterExample?: string[]
  shrinks?: number
  gaveUpAfter?: number
}

export interface PropertyResponse {
  available: boolean
  missing_binary: string | null
  items: PropertyResult[]
  error?: string
}

// Proof traces emitted by the proofTrace Lean binary
// (see ProofPilot/ProofTrace.lean). For each named theorem in
// Main.lean we get the statement, the axioms its proof transitively
// depends on (via Lean.collectAxioms), and a verified/sorry status.
export type ProofStatus = 'verified' | 'sorry' | 'missing'

export interface ProofTrace {
  name: string
  title: string
  description: string
  kind?: 'theorem' | 'definition'
  type?: string
  status: ProofStatus
  axioms?: string[]
  proofTermDepth?: number
}

export interface ProofResponse {
  available: boolean
  missing_binary: string | null
  items: ProofTrace[]
  error?: string
}
