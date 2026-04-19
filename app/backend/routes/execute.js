import { execSync }   from 'child_process';
import { readFileSync } from 'fs';
import { fileURLToPath } from 'url';
import path from 'path';
import Database from 'better-sqlite3';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const DATA_DIR  = path.join(__dirname, '..', 'data');
const JSON_FILE = path.join(DATA_DIR, 'users.json');
const DB_FILE   = path.join(DATA_DIR, 'users.db');

// ── SQLite bootstrap ────────────────────────────────────────────────────────

function getDb() {
  const db = new Database(DB_FILE);
  db.exec(`
    CREATE TABLE IF NOT EXISTS users (
      id    INTEGER PRIMARY KEY,
      name  TEXT    NOT NULL,
      age   INTEGER NOT NULL,
      email TEXT    NOT NULL
    );
  `);
  const count = db.prepare('SELECT COUNT(*) as n FROM users').get().n;
  if (count === 0) {
    const rows = JSON.parse(readFileSync(JSON_FILE, 'utf8'));
    const insert = db.prepare('INSERT INTO users VALUES (@id, @name, @age, @email)');
    const insertAll = db.transaction(rs => rs.forEach(r => insert.run(r)));
    insertAll(rows);
  }
  return db;
}

// ── jq execution ────────────────────────────────────────────────────────────

export function runJq(jqExpr) {
  try {
    const out = execSync(`jq '${jqExpr.replace(/'/g, "'\\''")}' ${JSON_FILE}`, {
      encoding: 'utf8',
      timeout:  5000,
    });
    return { ok: true, result: JSON.parse(out) };
  } catch (err) {
    return { ok: false, error: err.message };
  }
}

// ── SQL execution ────────────────────────────────────────────────────────────

export function runSql(sqlExpr) {
  try {
    const db   = getDb();
    const rows = db.prepare(sqlExpr).all();
    return { ok: true, result: rows };
  } catch (err) {
    return { ok: false, error: err.message };
  }
}
