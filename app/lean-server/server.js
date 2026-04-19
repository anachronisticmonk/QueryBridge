import express     from 'express';
import cors        from 'cors';
import { execSync } from 'child_process';
import path        from 'path';
import { fileURLToPath } from 'url';

const __dirname      = path.dirname(fileURLToPath(import.meta.url));
const PROOFPILOT_DIR = path.resolve(__dirname, '../../ProofPilot');
const LAKE           = process.env.LAKE_BIN || 'lake';

const app = express();
app.use(cors());
app.use(express.json());

/*
 * POST /verify
 * Body: { jquery: { type: "find"|"delete", pred: { field, op, value } } }
 *
 * Possible responses:
 *  { verified: true,  theorem, covers }         — proof applies
 *  { verified: false, reason: "out_of_scope" }  — query type not yet proved
 *  { verified: false, reason: "proof_broken",
 *    hint: "lake build failed" }                — proof doesn't compile
 *  { verified: false, reason: "parse_error" }   — bad JSON input
 */
app.post('/verify', (req, res) => {
  const { jquery } = req.body;
  if (!jquery) return res.status(400).json({ error: 'jquery field required' });

  const input = JSON.stringify(jquery).replace(/'/g, "'\\''");

  try {
    const stdout = execSync(
      `cd "${PROOFPILOT_DIR}" && ${LAKE} exe proofpilot '${input}'`,
      { encoding: 'utf8', timeout: 30_000 }
    ).trim();

    const lines   = stdout.split('\n');
    const status  = lines[0]?.trim();

    if (status === 'verified') {
      return res.json({
        verified: true,
        theorem:  lines[1]?.replace('theorem: ', '').trim(),
        covers:   lines[2]?.replace('covers: ',  '').trim(),
      });
    }

    if (status === 'out_of_scope') {
      return res.json({
        verified: false,
        reason:   'out_of_scope',
        detail:   lines[1]?.replace('reason: ', '').trim(),
      });
    }

    return res.json({ verified: false, reason: 'unknown_output', raw: stdout });

  } catch (err) {
    const msg = err.message ?? '';
    const stderr = err.stderr?.toString() ?? '';

    // lake build failure means a proof is broken or missing
    if (msg.includes('error:') || stderr.includes('error:')) {
      return res.status(200).json({
        verified: false,
        reason:   'proof_broken',
        hint:     'lake build failed — proof is incomplete or a new construct needs a theorem',
        detail:   stderr.slice(0, 600),
      });
    }

    if (msg.includes('no such file') || msg.includes('lake exe')) {
      return res.status(503).json({
        error: 'ProofPilot not built',
        hint:  `cd ProofPilot && lake build`,
      });
    }

    return res.status(500).json({ error: msg.slice(0, 400) });
  }
});

app.get('/health', (_req, res) =>
  res.json({ proofpilot: PROOFPILOT_DIR, status: 'ok' })
);

const PORT = process.env.PORT || 4000;
app.listen(PORT, () =>
  console.log(`lean-server :${PORT}  ProofPilot → ${PROOFPILOT_DIR}`)
);
