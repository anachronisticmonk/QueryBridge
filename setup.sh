#!/usr/bin/env bash
set -e

echo "==> QueryBridge setup"

# ── Homebrew ────────────────────────────────────────────────────────────────
if ! command -v brew &>/dev/null; then
  echo "==> Installing Homebrew..."
  /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
fi

# ── Python 3 ────────────────────────────────────────────────────────────────
if ! command -v python3 &>/dev/null; then
  echo "==> Installing Python via Homebrew..."
  brew install python
fi

# ── Node.js ─────────────────────────────────────────────────────────────────
if ! command -v node &>/dev/null; then
  echo "==> Installing Node.js via Homebrew..."
  brew install node
fi

# ── Backend virtualenv ───────────────────────────────────────────────────────
echo "==> Setting up Python virtualenv..."
cd backend
python3 -m venv .venv
.venv/bin/pip install -q --upgrade pip
.venv/bin/pip install -q -r requirements.txt
if [ ! -f .env ]; then
  cp .env.example .env
  echo ""
  echo "  NOTE: backend/.env created from .env.example."
  echo "        Add your ANTHROPIC_API_KEY there to use the real LLM."
  echo "        The app works without it — just keep 'Mock LLM' checked in the UI."
  echo ""
fi
cd ..

# ── Frontend ────────────────────────────────────────────────────────────────
echo "==> Installing frontend dependencies..."
cd frontend
npm install --silent
cd ..

echo ""
echo "✓ Setup complete."
echo ""
echo "Run the app (two terminals):"
echo ""
echo "  Terminal 1 — backend:"
echo "    cd backend && .venv/bin/uvicorn main:app --port 8000 --reload"
echo ""
echo "  Terminal 2 — frontend:"
echo "    cd frontend && npm run dev"
echo ""
echo "  Then open http://localhost:5173"
echo ""
