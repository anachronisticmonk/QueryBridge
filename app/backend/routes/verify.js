const LEAN_SERVER = process.env.LEAN_SERVER_URL || 'http://localhost:4000';

export async function verifyWithLean(jquery) {
  if (!jquery) {
    return { verified: false, reason: 'out_of_scope', detail: 'query could not be expressed as JQuery' };
  }

  const res = await fetch(`${LEAN_SERVER}/verify`, {
    method:  'POST',
    headers: { 'Content-Type': 'application/json' },
    body:    JSON.stringify({ jquery }),
  });

  if (res.status === 503) {
    const body = await res.json().catch(() => ({}));
    return { verified: false, reason: 'not_built', hint: body.hint };
  }

  if (!res.ok) {
    const body = await res.json().catch(() => ({}));
    throw new Error(body.error ?? `lean-server ${res.status}`);
  }

  return res.json();
}
