export default function VerificationWidget({ verification, jquery }) {
  if (!verification) return null;

  // ── Verified ──────────────────────────────────────────────────────────────
  if (verification.verified === true) {
    return (
      <div className="verification-widget lean-ok">
        <span className="v-icon">✓</span>
        <div className="v-body">
          <span className="v-title">Lean verified — semantically equivalent</span>
          <span className="v-detail">{verification.theorem}</span>
          <span className="v-detail">{verification.covers}</span>
        </div>
        {jquery && <JQueryBadge jquery={jquery} />}
      </div>
    );
  }

  // ── Out of scope ──────────────────────────────────────────────────────────
  if (verification.reason === 'out_of_scope') {
    return (
      <div className="verification-widget lean-scope">
        <span className="v-icon">⊘</span>
        <div className="v-body">
          <span className="v-title">Out of proof scope</span>
          <span className="v-detail">
            {verification.detail ?? 'This query type is not yet covered by query_equiv.'}
          </span>
          <span className="v-detail muted">
            Add a constructor to JQuery/SQuery and extend the proof to enable verification.
          </span>
        </div>
      </div>
    );
  }

  // ── Proof broken ──────────────────────────────────────────────────────────
  if (verification.reason === 'proof_broken') {
    return (
      <div className="verification-widget lean-fail">
        <span className="v-icon">✗</span>
        <div className="v-body">
          <span className="v-title">Proof broken — lake build failed</span>
          <span className="v-detail">{verification.hint}</span>
          {verification.detail && (
            <pre className="v-code">{verification.detail}</pre>
          )}
        </div>
      </div>
    );
  }

  // ── Not built ─────────────────────────────────────────────────────────────
  if (verification.reason === 'not_built') {
    return (
      <div className="verification-widget lean-warn">
        <span className="v-icon">⚡</span>
        <div className="v-body">
          <span className="v-title">ProofPilot not built</span>
          <span className="v-detail">{verification.hint ?? 'cd ProofPilot && lake build'}</span>
        </div>
      </div>
    );
  }

  // ── Generic error ─────────────────────────────────────────────────────────
  return (
    <div className="verification-widget lean-warn">
      <span className="v-icon">⚡</span>
      <div className="v-body">
        <span className="v-title">Verification error</span>
        <span className="v-detail">{verification.error ?? JSON.stringify(verification)}</span>
      </div>
    </div>
  );
}

function JQueryBadge({ jquery }) {
  if (!jquery) return null;
  const { type, pred } = jquery;
  return (
    <div className="jquery-badge">
      <span className="jq-type">{type}</span>
      <span className="jq-pred">{pred.field} {pred.op} {pred.value}</span>
    </div>
  );
}
