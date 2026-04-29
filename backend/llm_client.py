"""LLM → jq translation with a mock fallback that requires no API key."""
import os
import re
from anthropic import Anthropic

_SYSTEM = """You translate natural language into jq expressions over a JSON array of user objects.
Each object has exactly three fields: name (string), age (number), role (one of "student" | "employee" | "retired").

You MUST output only a jq expression matching ONE of these patterns:
  1. .[]
  2. .[] | select(<predicate>)
  3. .[] | select(<predicate>) | .FIELD
  4. del(.[] | select(<predicate>))
  5. length
  6. .[] | insert("NAME", AGE, "ROLE")
  7. .[] | update(.FIELD, VALUE, <predicate>)

Predicates may combine leaf comparisons with `&&` (AND) or `||` (OR). Examples:
  .name == "Bob" && .age > 20
  .role == "student" || .age >= 30
Allowed fields: name, age, role
Allowed operators: == != > >= < <=
String and role values must be double-quoted.

Output the jq expression and nothing else. No explanation."""

# Mock rules: (positive_keywords, negative_keywords, jq_template_or_callable).
# Earlier rules win; specific rules first.
def _build(nl_lower: str) -> str | None:
    # 1. Insert: "insert/add a user with name X, age Y, role Z"
    m = re.search(r"(?:insert|add)\s+(?:a\s+)?user\s+(?:with\s+)?(?:name\s*)?['\"]?(\w+)['\"]?[,\s]+age\s*['\"]?(\d+)['\"]?[,\s]+(?:and\s+)?role\s*['\"]?(\w+)['\"]?", nl_lower)
    if m:
        name, age, role = m.group(1).capitalize(), m.group(2), m.group(3).lower()
        return f'.[] | insert("{name}", {age}, "{role}")'

    # 2. Update: "change/update/set FIELD to VALUE for/where ... CONDITION"
    #    "change the name to 'Vimala' for any user whose current name is 'Eve'"
    upd = re.search(
        r"(?:change|update|set)\s+(?:the\s+)?(\w+)\s+(?:to|=)\s+['\"]?(\w+)['\"]?"
        r".*?(?:where|whose|for\s+(?:any\s+)?user[s]?\s+whose|for\s+users?\s+(?:where|whose))\s+"
        r"(?:current\s+)?(\w+)\s+(?:is|=|==)\s+['\"]?(\w+)['\"]?",
        nl_lower,
    )
    if upd:
        col = upd.group(1)
        val_raw = upd.group(2)
        cond_col = upd.group(3)
        cond_val_raw = upd.group(4)
        val = val_raw if val_raw.isdigit() else f'"{val_raw.capitalize()}"' if col == 'name' else f'"{val_raw}"'
        cond_val = cond_val_raw if cond_val_raw.isdigit() else f'"{cond_val_raw.capitalize()}"' if cond_col == 'name' else f'"{cond_val_raw}"'
        return f'.[] | update(.{col}, {val}, .{cond_col} == {cond_val})'

    # 3. AND/OR queries: "find users whose name is Bob and age > 20"
    if any(k in nl_lower for k in ["name", "age", "role"]) and (" and " in nl_lower or " or " in nl_lower):
        leaves = []
        # Try to extract up to two leaf clauses joined by and/or
        op = "&&" if " and " in nl_lower else "||"
        # name is X
        m_name = re.search(r"name\s+(?:is|=|==)\s+['\"]?(\w+)['\"]?", nl_lower)
        if m_name:
            leaves.append(f'.name == "{m_name.group(1).capitalize()}"')
        # age > N / age < N etc.
        m_age = re.search(r"age\s+(?:is\s+)?(>=|<=|>|<|==|=|is)\s+['\"]?(\d+)['\"]?", nl_lower)
        if not m_age:
            m_age = re.search(r"age\s+(?:over|above|greater than|more than)\s+(\d+)", nl_lower)
            if m_age:
                leaves.append(f'.age > {m_age.group(1)}')
                m_age = None
            else:
                m_age2 = re.search(r"age\s+(?:under|below|less than|younger than)\s+(\d+)", nl_lower)
                if m_age2:
                    leaves.append(f'.age < {m_age2.group(1)}')
                    m_age = None
        if m_age:
            op_raw, num = m_age.group(1), m_age.group(2)
            op_map = {"=": "==", "is": "=="}
            jq_op = op_map.get(op_raw, op_raw)
            leaves.append(f'.age {jq_op} {num}')
        # role is X
        m_role = re.search(r"role\s+(?:is|=|==)\s+['\"]?(student|employee|retired)['\"]?", nl_lower)
        if m_role:
            leaves.append(f'.role == "{m_role.group(1)}"')
        if len(leaves) >= 2:
            return f".[] | select({leaves[0]} {op} {leaves[1]})"

    # 4. Role queries: "find users whose role is employee"
    m = re.search(r"role\s+(?:is\s+)?['\"]?(student|employee|retired)['\"]?", nl_lower)
    if m and any(k in nl_lower for k in ["find", "show", "list", "get", "who", "users", "people"]):
        return f'.[] | select(.role == "{m.group(1)}")'

    # 5. Count
    if any(k in nl_lower for k in ["how many", "count", "number of"]):
        return "length"

    return None


_MOCK_RULES: list[tuple[list[str], list[str], str]] = [
    (["delet", "remov"],  ["young", "< 25", "under 25", "less than 25", "below 25"],   "del(.[] | select(.age < 25))"),
    (["delet", "remov"],  ["old", "> 30", "over 30", "older than 30", "above 30"],     "del(.[] | select(.age > 30))"),
    (["name", "names"],   ["over 30", "> 30", "older than 30", "above 30"],            ".[] | select(.age > 30) | .name"),
    (["name", "names"],   ["young", "< 25", "under 25", "less than 25"],               ".[] | select(.age < 25) | .name"),
    (["alice"],           [],                                                           '.[] | select(.name == "Alice")'),
    (["bob"],             [],                                                           '.[] | select(.name == "Bob")'),
    ([],                  ["young", "< 25", "under 25", "less than 25", "below 25"],   ".[] | select(.age < 25)"),
    ([],                  ["over 30", "> 30", "older than 30", "above 30"],            ".[] | select(.age > 30)"),
    ([],                  ["over 35", "> 35", "older than 35", "above 35"],            ".[] | select(.age > 35)"),
    (["all", "every", "show", "list", "get"], ["user", "people", "person", ""],        ".[]"),
]


def _mock(nl: str) -> str:
    nl_lower = nl.lower()
    # Try the higher-priority structured matchers first.
    structured = _build(nl_lower)
    if structured is not None:
        return structured
    for pos_kws, neg_kws, jq in _MOCK_RULES:
        pos_match = not pos_kws or any(k in nl_lower for k in pos_kws)
        neg_match = not neg_kws or any(k in nl_lower for k in neg_kws)
        if pos_match and neg_match:
            return jq
    return ".[]"


def nl_to_jq(natural_language: str, use_mock: bool = True) -> str:
    if use_mock:
        return _mock(natural_language)

    client = Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
    msg = client.messages.create(
        model="claude-sonnet-4-6",
        max_tokens=128,
        system=_SYSTEM,
        messages=[{"role": "user", "content": natural_language}],
    )
    return msg.content[0].text.strip()
