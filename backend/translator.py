"""
jq → SQL translator.

Mirrors the Lean proof's jqueryToSquery mapping for the supported subset:
  JQuery.find    col pred  →  SQuery.select col pred
  JQuery.drop    pred      →  SQuery.delete pred
  JQuery.prepend usr       →  SQuery.insert usr
  JQuery.count             →  SQuery.count
  JQuery.modify  col v c   →  SQuery.update col v c

Supported jq patterns:
  .[]
  .[] | select(<predicate>)
  .[] | select(<predicate>) | .FIELD
  del(.[] | select(<predicate>))
  del(.[])
  length
  .[] | insert("name", age, "role")
  .[] | update(.field, value, <predicate>)

Predicates are leaf comparisons combined with `&&` or `||`:
  .field op value
  PRED && PRED
  PRED || PRED
"""
import re

_OP = {"==": "=", "!=": "!=", ">": ">", ">=": ">=", "<": "<", "<=": "<="}

_UNSUPPORTED_MSG = (
    "Unsupported jq pattern.\n\n"
    "Supported forms:\n"
    "  .[]\n"
    "  .[] | select(<predicate>)\n"
    "  .[] | select(<predicate>) | .col\n"
    "  del(.[] | select(<predicate>))\n"
    "  del(.[])\n"
    "  length\n"
    '  .[] | insert("name", age, "role")\n'
    "  .[] | update(.col, value, <predicate>)\n\n"
    "Predicates: leaf  .field op value  combined with && / ||\n"
    "Operators:  == != > >= < <="
)


_LEAF_RE = re.compile(
    r'\.(\w+)\s*(==|!=|>=|<=|>|<)\s*(?:"([^"]*)"|([\-\d.]+))'
)


def _parse_leaf(s: str) -> dict:
    m = _LEAF_RE.match(s.strip())
    if not m:
        raise ValueError(f"Cannot parse predicate leaf: {s!r}")
    field = m.group(1)
    cmp = m.group(2)
    if m.group(3) is not None:
        return {"op": "leaf", "field": field, "cmp": cmp, "value": m.group(3), "str": True}
    return {"op": "leaf", "field": field, "cmp": cmp, "value": m.group(4), "str": False}


def parse_pred(s: str) -> dict:
    """Parse a flat predicate (no nested parens) into a small AST."""
    s = s.strip()
    if "||" in s:
        return {"op": "or", "parts": [parse_pred(p) for p in s.split("||")]}
    if "&&" in s:
        return {"op": "and", "parts": [parse_pred(p) for p in s.split("&&")]}
    return _parse_leaf(s)


def pred_to_sql(t: dict) -> str:
    if t["op"] == "leaf":
        v = f"'{t['value']}'" if t["str"] else t["value"]
        return f"{t['field']} {_OP[t['cmp']]} {v}"
    sep = " AND " if t["op"] == "and" else " OR "
    return "(" + sep.join(pred_to_sql(p) for p in t["parts"]) + ")"


def _coerce(raw: str, is_str: bool):
    if is_str:
        return raw
    return int(raw) if "." not in raw else float(raw)


def pred_eval(user: dict, t: dict) -> bool:
    if t["op"] == "leaf":
        actual = user.get(t["field"])
        target = _coerce(t["value"], t["str"])
        cmp = t["cmp"]
        if cmp == "==": return actual == target
        if cmp == "!=": return actual != target
        if actual is None or target is None: return False
        if cmp == ">":  return actual > target
        if cmp == ">=": return actual >= target
        if cmp == "<":  return actual < target
        if cmp == "<=": return actual <= target
        return False
    parts = [pred_eval(user, p) for p in t["parts"]]
    return any(parts) if t["op"] == "or" else all(parts)


_INSERT_RE = re.compile(
    r'\.\[\]\s*\|\s*insert\(\s*"([^"]*)"\s*,\s*(\d+)\s*,\s*"(\w+)"\s*\)\s*$'
)
_UPDATE_RE = re.compile(
    r'\.\[\]\s*\|\s*(?:update|modify)\(\s*\.(\w+)\s*,\s*("[^"]*"|\d+)\s*,\s*(.+?)\s*\)\s*$'
)


def translate(jq_expr: str) -> dict:
    """
    Returns a dict shaped:
      type        : "find" | "delete" | "count" | "insert" | "update"
      col         : column name or None
      pred_tree   : predicate AST (or None)
      sql         : executable SQL string
      display_sql : nicely formatted SQL for the UI
      insert_user : tuple (name, age, role) for type=insert (else None)
      update_col  : column name for type=update (else None)
      update_value: raw value (str or int) for type=update (else None)
    """
    jq = jq_expr.strip()

    # length — count aggregate
    if jq == "length":
        return {
            "type": "count",
            "col": None,
            "pred_tree": None,
            "sql": "SELECT COUNT(*) AS count FROM users",
            "display_sql": "SELECT COUNT(*) AS count\nFROM users",
            "insert_user": None,
            "update_col": None,
            "update_value": None,
        }

    # .[] | insert("name", age, "role")
    m = _INSERT_RE.match(jq)
    if m:
        name, age, role = m.group(1), int(m.group(2)), m.group(3)
        return {
            "type": "insert",
            "col": None,
            "pred_tree": None,
            "sql": f"INSERT INTO users VALUES ('{name}', {age}, '{role}')",
            "display_sql": f"INSERT INTO users\nVALUES ('{name}', {age}, '{role}')",
            "insert_user": {"name": name, "age": age, "role": role},
            "update_col": None,
            "update_value": None,
        }

    # .[] | update(.col, value, <predicate>)
    m = _UPDATE_RE.match(jq)
    if m:
        col = m.group(1)
        raw_val = m.group(2)
        if raw_val.startswith('"'):
            sql_val = f"'{raw_val[1:-1]}'"
            py_val = raw_val[1:-1]
        else:
            sql_val = raw_val
            py_val = int(raw_val)
        pred_str = m.group(3).strip()
        # Parse the predicate AST. The Lean parser can return Cond.always for
        # an empty/unparseable predicate; allow that too.
        try:
            tree = parse_pred(pred_str)
            sql_where = pred_to_sql(tree)
        except ValueError:
            tree = None
            sql_where = "TRUE"
        return {
            "type": "update",
            "col": col,
            "pred_tree": tree,
            "sql": f"UPDATE users SET {col} = {sql_val} WHERE {sql_where}",
            "display_sql": f"UPDATE users\nSET {col} = {sql_val}\nWHERE {sql_where}",
            "insert_user": None,
            "update_col": col,
            "update_value": py_val,
        }

    # del(.[]) — unconditional delete (mirrors Lean's JQuery.clear → SQuery.truncate)
    if re.match(r'^del\(\s*\.\[\]\s*\)$', jq):
        return {
            "type": "delete",
            "col": None,
            "pred_tree": None,
            "sql": "DELETE FROM users",
            "display_sql": "DELETE FROM users",
            "insert_user": None,
            "update_col": None,
            "update_value": None,
        }

    # del(.[] | select(PRED))
    m = re.match(r'del\(\s*\.\[\]\s*\|\s*select\((.+?)\)\s*\)$', jq)
    if m:
        pred_str = m.group(1).strip()
        tree = parse_pred(pred_str)
        sql_where = pred_to_sql(tree)
        return {
            "type": "delete",
            "col": None,
            "pred_tree": tree,
            "sql": f"DELETE FROM users WHERE {sql_where}",
            "display_sql": f"DELETE FROM users\nWHERE {sql_where}",
            "insert_user": None,
            "update_col": None,
            "update_value": None,
        }

    # .[] | select(PRED) | .col
    m = re.match(r'\.\[\]\s*\|\s*select\((.+?)\)\s*\|\s*\.(\w+)$', jq)
    if m:
        pred_str = m.group(1).strip()
        col = m.group(2)
        tree = parse_pred(pred_str)
        sql_where = pred_to_sql(tree)
        return {
            "type": "find",
            "col": col,
            "pred_tree": tree,
            "sql": f"SELECT {col} FROM users WHERE {sql_where}",
            "display_sql": f"SELECT {col}\nFROM users\nWHERE {sql_where}",
            "insert_user": None,
            "update_col": None,
            "update_value": None,
        }

    # .[] | select(PRED)
    m = re.match(r'\.\[\]\s*\|\s*select\((.+)\)$', jq)
    if m:
        pred_str = m.group(1).strip()
        tree = parse_pred(pred_str)
        sql_where = pred_to_sql(tree)
        return {
            "type": "find",
            "col": None,
            "pred_tree": tree,
            "sql": f"SELECT * FROM users WHERE {sql_where}",
            "display_sql": f"SELECT *\nFROM users\nWHERE {sql_where}",
            "insert_user": None,
            "update_col": None,
            "update_value": None,
        }

    # .[]
    if jq == ".[]":
        return {
            "type": "find",
            "col": None,
            "pred_tree": None,
            "sql": "SELECT * FROM users",
            "display_sql": "SELECT *\nFROM users",
            "insert_user": None,
            "update_col": None,
            "update_value": None,
        }

    raise ValueError(_UNSUPPORTED_MSG)
