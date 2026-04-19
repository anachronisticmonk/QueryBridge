import Anthropic      from '@anthropic-ai/sdk';
import { readFileSync } from 'fs';
import path             from 'path';
import { fileURLToPath } from 'url';

const client = new Anthropic();

// ── Contract file owned by ProofPilot ────────────────────────────────────
// When a new operation is added to QueryEquiv.lean, update query-ops.json.
// This file is read once at startup — restart the backend to pick up changes.
const OPS_PATH = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  '../../../ProofPilot/query-ops.json'
);

function loadOps() {
  try {
    return JSON.parse(readFileSync(OPS_PATH, 'utf8'));
  } catch {
    console.warn(`⚠ Could not read ${OPS_PATH} — using empty ops`);
    return { operations: [], pred_fields: [], pred_ops: [] };
  }
}

const ops = loadOps();

const OPS_SUMMARY = ops.operations
  .map(o => `  - "${o.type}": ${o.description} (SQL: ${o.sql_equivalent})`)
  .join('\n');

const SYSTEM = `You translate natural-language queries about a users dataset into queries.
Return ONLY a raw JSON object (no markdown) with keys:
- "jq"  : jq expression on an array of {name:string, age:number} objects
- "sql" : equivalent SQL statement (table name: users, columns: name, age)
- "jquery": { "type": <one of the supported types below>, "pred": { "field": one of [${ops.pred_fields.join(', ')}], "op": one of [${ops.pred_ops.join(', ')}], "value": <number> } }
  Set "jquery" to null if the request cannot be expressed as a single-predicate operation.

Supported jquery types (proven in Lean):
${OPS_SUMMARY || '  (none yet — set jquery to null)'}`;

export async function generateQueries(nlQuery) {
  if (process.env.MOCK_CLAUDE === 'true') return mockGenerate(nlQuery);

  try {
    const msg = await client.messages.create({
      model:      'claude-haiku-4-5-20251001',
      max_tokens: 512,
      system:     SYSTEM,
      messages:   [{ role: 'user', content: nlQuery }],
    });
    const raw = msg.content[0].text.trim().replace(/^```json?\n?/, '').replace(/\n?```$/, '');
    return JSON.parse(raw);
  } catch (err) {
    if (err.status === 400 && err.message?.includes('credit')) {
      console.warn('⚠ Billing — falling back to mock.');
      return mockGenerate(nlQuery);
    }
    throw err;
  }
}

function mockGenerate(nlQuery) {
  const q   = nlQuery.toLowerCase();
  const age = Number(q.match(/\d+/)?.[0] ?? 10);

  if (q.includes('under') || q.includes('less') || q.includes('below') || q.includes('younger')) {
    return {
      jq:     `[.[] | select(.age < ${age}) | .name]`,
      sql:    `SELECT name FROM users WHERE age < ${age}`,
      jquery: { type: 'find', pred: { field: 'age', op: 'lt', value: age } },
    };
  }
  if (q.includes('over') || q.includes('older') || q.includes('above') || q.includes('greater')) {
    return {
      jq:     `[.[] | select(.age > ${age}) | .name]`,
      sql:    `SELECT name FROM users WHERE age > ${age}`,
      jquery: { type: 'find', pred: { field: 'age', op: 'gt', value: age } },
    };
  }
  if (q.includes('delete') || q.includes('remove')) {
    return {
      jq:     `[.[] | select(.age < ${age} | not)]`,
      sql:    `DELETE FROM users WHERE age < ${age}`,
      jquery: { type: 'delete', pred: { field: 'age', op: 'lt', value: age } },
    };
  }
  return { jq: `[.[] | {name,age}]`, sql: `SELECT name, age FROM users`, jquery: null };
}
