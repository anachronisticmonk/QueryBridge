import 'dotenv/config';
import express from 'express';
import cors    from 'cors';
import { generateQueries } from './routes/generate.js';
import { runJq }           from './routes/execute.js';
import { verifyWithLean }  from './routes/verify.js';

const app = express();
app.use(cors());
app.use(express.json());

app.post('/api/run', async (req, res) => {
  const { query } = req.body;
  if (!query) return res.status(400).json({ error: 'query is required' });

  try {
    const { jq, sql, jquery } = await generateQueries(query);

    const [verif, exec] = await Promise.allSettled([
      verifyWithLean(jquery),
      Promise.resolve(runJq(jq)),
    ]);

    res.json({
      jq,
      sql,
      jquery,
      jqResult:     exec.status === 'fulfilled'  ? exec.value  : { ok: false, error: exec.reason?.message },
      verification: verif.status === 'fulfilled' ? verif.value : { verified: null, error: verif.reason?.message },
    });
  } catch (err) {
    console.error(err);
    res.status(500).json({ error: err.message });
  }
});

app.get('/health', (_req, res) => res.json({ status: 'ok' }));

const PORT = process.env.PORT || 3001;
app.listen(PORT, () => console.log(`backend :${PORT}`));
