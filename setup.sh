#!/usr/bin/env bash
set -euo pipefail

# ── Colours ──────────────────────────────────────────────────────────────────
GREEN='\033[0;32m'; YELLOW='\033[1;33m'; RED='\033[0;31m'; NC='\033[0m'
ok()   { echo -e "${GREEN}✓${NC}  $*"; }
info() { echo -e "${YELLOW}→${NC}  $*"; }
die()  { echo -e "${RED}✗${NC}  $*" >&2; exit 1; }

echo ""
echo "  ProofPilot — setup"
echo "  ──────────────────"
echo ""

# ── 1. Homebrew (macOS only) ──────────────────────────────────────────────────
if [[ "$(uname)" == "Darwin" ]]; then
  if ! command -v brew &>/dev/null; then
    info "Installing Homebrew..."
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    ok "Homebrew installed"
  else
    ok "Homebrew present"
  fi
fi

# ── 2. Node / npm ─────────────────────────────────────────────────────────────
if ! command -v node &>/dev/null; then
  info "Installing Node.js via nvm..."
  curl -fsSL https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.7/install.sh | bash
  export NVM_DIR="$HOME/.nvm"
  # shellcheck source=/dev/null
  source "$NVM_DIR/nvm.sh"
  nvm install --lts
  nvm use --lts
  ok "Node $(node --version) installed"
else
  ok "Node $(node --version) present"
fi

if ! command -v npm &>/dev/null; then
  die "npm not found even after Node install — please install manually"
fi

# ── 3. jq CLI (needed by backend to run jq queries) ──────────────────────────
if ! command -v jq &>/dev/null; then
  info "Installing jq..."
  if [[ "$(uname)" == "Darwin" ]]; then
    brew install jq
  elif command -v apt-get &>/dev/null; then
    sudo apt-get install -y jq
  elif command -v dnf &>/dev/null; then
    sudo dnf install -y jq
  else
    die "Cannot install jq automatically — please install it manually: https://jqlang.github.io/jq/"
  fi
  ok "jq installed"
else
  ok "jq $(jq --version) present"
fi

# ── 4. Lean / elan ───────────────────────────────────────────────────────────
if ! command -v elan &>/dev/null; then
  info "Installing elan (Lean version manager)..."
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
  export PATH="$HOME/.elan/bin:$PATH"
  ok "elan installed"
else
  ok "elan present"
fi

export PATH="$HOME/.elan/bin:$PATH"

# ── 5. npm install for all three Node services ────────────────────────────────
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

for svc in backend lean-server frontend; do
  dir="$SCRIPT_DIR/app/$svc"
  if [[ -f "$dir/package.json" ]]; then
    info "npm install → app/$svc"
    (cd "$dir" && npm install --silent)
    ok "app/$svc"
  fi
done

# ── 6. .env for backend ───────────────────────────────────────────────────────
ENV_FILE="$SCRIPT_DIR/app/backend/.env"
EXAMPLE="$SCRIPT_DIR/app/backend/.env.example"
if [[ ! -f "$ENV_FILE" ]]; then
  cp "$EXAMPLE" "$ENV_FILE"
  info ".env created from .env.example — add your ANTHROPIC_API_KEY to app/backend/.env"
else
  ok ".env already exists"
fi

# ── 7. Lean build ─────────────────────────────────────────────────────────────
PROOFPILOT="$SCRIPT_DIR/ProofPilot"
info "lake update (fetching Mathlib — this can take a few minutes the first time)..."
(cd "$PROOFPILOT" && lake update)
info "lake build..."
if (cd "$PROOFPILOT" && lake build); then
  ok "ProofPilot built"
else
  echo ""
  echo -e "${YELLOW}⚠ lake build failed.${NC}"
  echo "  This usually means a proof is incomplete (expected during development)."
  echo "  The system will still run but will show 'Proof broken' in the UI."
  echo "  Fix the proof in ProofPilot/ProofPilot/Lang/QueryEquiv.lean and re-run:"
  echo "    cd ProofPilot && lake build"
fi

# ── Done ──────────────────────────────────────────────────────────────────────
echo ""
echo "  ─────────────────────────────────────────────────────────"
echo "  Setup complete. Start the stack in three terminals:"
echo ""
echo "    cd app/lean-server && node server.js"
echo "    cd app/backend     && node server.js"
echo "    cd app/frontend    && npm run dev"
echo ""
echo "  Add ANTHROPIC_API_KEY to app/backend/.env before starting."
echo "  UI → http://localhost:5173"
echo "  ─────────────────────────────────────────────────────────"
echo ""
