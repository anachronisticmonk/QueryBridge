"""
jq → SQL translator.

Mirrors the Lean proof's jqueryToSquery mapping exactly:
  JQuery.find col pred  →  SQuery.select col pred
  JQuery.delete pred    →  SQuery.drop pred

Supported jq patterns:
  .[]
  .[] | select(.FIELD OP VALUE)
  .[] | select(.FIELD OP VALUE) | .FIELD
  del(.[] | select(.FIELD OP VALUE))
"""
import re

_OP = {"==": "=", "!=": "!=", ">": ">", ">=": ">=", "<": "<", "<=": "<="}

_UNSUPPORTED_MSG = (
    "Unsupported jq pattern.\n\n"
    "Supported forms:\n"
    "  .[]                                           — select all\n"
    "  .[] | select(.field op value)                — filter rows\n"
    "  .[] | select(.field op value) | .col         — filter + project\n"
    "  del(.[] | select(.field op value))           — delete rows\n\n"
    "Operators: == != > >= < <="
)


def _parse_pred(pred: str) -> tuple[str, str, str]:
    """Parse '.field op value' → (field, sql_op, sql_value)."""
    m = re.match(
        r'\.(\w+)\s*(==|!=|>=|<=|>|<)\s*(?:"([^"]*)"|([\d.]+))',
        pred.strip(),
    )
    if not m:
        raise ValueError(f"Cannot parse predicate: {pred!r}")
    field = m.group(1)
    sql_op = _OP[m.group(2)]
    sql_val = f"'{m.group(3)}'" if m.group(3) is not None else m.group(4)
    return field, sql_op, sql_val


def translate(jq_expr: str) -> dict:
    """
    Returns:
        type        : "find" | "delete"
        col         : column name or None (None = all columns)
        pred_jq     : raw predicate string or None
        pred_sql    : SQL predicate fragment or None
        sql         : executable SQL string
        display_sql : nicely formatted SQL for the UI
    """
    jq = jq_expr.strip()

    # del(.[] | select(PRED))
    m = re.match(r'del\(\s*\.\[\]\s*\|\s*select\((.+?)\)\s*\)$', jq)
    if m:
        pred_jq = m.group(1).strip()
        field, op, val = _parse_pred(pred_jq)
        pred_sql = f"{field} {op} {val}"
        return {
            "type": "delete",
            "col": None,
            "pred_jq": pred_jq,
            "pred_sql": pred_sql,
            "sql": f"DELETE FROM users WHERE {pred_sql}",
            "display_sql": f"DELETE FROM users\nWHERE {pred_sql}",
        }

    # .[] | select(PRED) | .col
    m = re.match(r'\.\[\]\s*\|\s*select\((.+?)\)\s*\|\s*\.(\w+)$', jq)
    if m:
        pred_jq = m.group(1).strip()
        col = m.group(2)
        field, op, val = _parse_pred(pred_jq)
        pred_sql = f"{field} {op} {val}"
        return {
            "type": "find",
            "col": col,
            "pred_jq": pred_jq,
            "pred_sql": pred_sql,
            "sql": f"SELECT {col} FROM users WHERE {pred_sql}",
            "display_sql": f"SELECT {col}\nFROM users\nWHERE {pred_sql}",
        }

    # .[] | select(PRED)
    m = re.match(r'\.\[\]\s*\|\s*select\((.+)\)$', jq)
    if m:
        pred_jq = m.group(1).strip()
        field, op, val = _parse_pred(pred_jq)
        pred_sql = f"{field} {op} {val}"
        return {
            "type": "find",
            "col": None,
            "pred_jq": pred_jq,
            "pred_sql": pred_sql,
            "sql": f"SELECT * FROM users WHERE {pred_sql}",
            "display_sql": f"SELECT *\nFROM users\nWHERE {pred_sql}",
        }

    # .[]
    if jq == ".[]":
        return {
            "type": "find",
            "col": None,
            "pred_jq": None,
            "pred_sql": None,
            "sql": "SELECT * FROM users",
            "display_sql": "SELECT *\nFROM users",
        }

    raise ValueError(_UNSUPPORTED_MSG)
