"""Execute jq-equivalent queries on in-memory JSON and SQL (SQLite)."""
import sqlite3

from translator import pred_eval


def run_jq(data: list[dict], query: dict) -> list:
    """Mirror of the Lean eval_jquery function for the supported subset."""
    qtype = query["type"]
    pred = query.get("pred_tree")
    col = query.get("col")

    if qtype == "count":
        return [{"count": len(data)}]

    if qtype == "insert":
        u = query["insert_user"]
        return [u] + list(data)

    if qtype == "update":
        target_col = query["update_col"]
        target_val = query["update_value"]

        def upd(u: dict) -> dict:
            if pred is None or pred_eval(u, pred):
                return {**u, target_col: target_val}
            return u
        return [upd(u) for u in data]

    if qtype == "delete":
        # Survivors — rows that do NOT match the predicate
        if pred is None:
            return []
        return [u for u in data if not pred_eval(u, pred)]

    # find
    if pred is not None:
        filtered = [u for u in data if pred_eval(u, pred)]
    else:
        filtered = list(data)
    if col:
        return [u[col] for u in filtered if col in u]
    return filtered


def run_sql(sql: str, data: list[dict]) -> tuple[list[str], list[dict]]:
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    cur = conn.cursor()
    cur.execute("CREATE TABLE users (name TEXT, age INTEGER, role TEXT)")
    cur.executemany(
        "INSERT INTO users VALUES (?, ?, ?)",
        [(u["name"], u["age"], u.get("role", "")) for u in data],
    )
    conn.commit()

    upper = sql.strip().upper()
    if upper.startswith(("DELETE", "INSERT", "UPDATE")):
        cur.execute(sql)
        conn.commit()
        cur.execute("SELECT * FROM users")
    else:
        cur.execute(sql)

    rows = cur.fetchall()
    if not rows:
        cols: list[str] = []
        conn.close()
        return cols, []
    cols = list(rows[0].keys())
    result = [dict(r) for r in rows]
    conn.close()
    return cols, result
