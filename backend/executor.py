"""Execute jq-equivalent queries on in-memory JSON and SQL (SQLite)."""
import re
import sqlite3


_OP_FNS = {
    "==": lambda a, b: a == b,
    "!=": lambda a, b: a != b,
    ">":  lambda a, b: a > b,
    ">=": lambda a, b: a >= b,
    "<":  lambda a, b: a < b,
    "<=": lambda a, b: a <= b,
}


def _eval_pred(user: dict, pred_jq: str) -> bool:
    m = re.match(
        r'\.(\w+)\s*(==|!=|>=|<=|>|<)\s*(?:"([^"]*)"|([\d.]+))',
        pred_jq.strip(),
    )
    if not m:
        return True
    field = m.group(1)
    op_fn = _OP_FNS[m.group(2)]
    if m.group(3) is not None:
        value: str | int = m.group(3)
    else:
        raw = m.group(4)
        value = int(raw) if "." not in raw else float(raw)
    return op_fn(user.get(field), value)


def run_jq(data: list[dict], query: dict) -> list:
    pred_jq = query.get("pred_jq")
    col = query.get("col")

    if query["type"] == "count":
        return [{"count": len(data)}]

    if query["type"] == "delete":
        # Return survivors (rows that do NOT match the predicate)
        return [u for u in data if not _eval_pred(u, pred_jq)]

    # find
    filtered = [u for u in data if _eval_pred(u, pred_jq)] if pred_jq else list(data)
    if col:
        return [u[col] for u in filtered if col in u]
    return filtered


def run_sql(sql: str, data: list[dict]) -> tuple[list[str], list[dict]]:
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    cur = conn.cursor()
    cur.execute("CREATE TABLE users (name TEXT, age INTEGER)")
    cur.executemany(
        "INSERT INTO users VALUES (?, ?)",
        [(u["name"], u["age"]) for u in data],
    )
    conn.commit()

    if sql.strip().upper().startswith("DELETE"):
        cur.execute(sql)
        conn.commit()
        cur.execute("SELECT * FROM users")
    else:
        cur.execute(sql)

    rows = cur.fetchall()
    if not rows:
        cols: list[str] = []
        return cols, []
    cols = list(rows[0].keys())
    result = [dict(r) for r in rows]
    conn.close()
    return cols, result
