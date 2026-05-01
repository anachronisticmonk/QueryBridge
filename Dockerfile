# syntax=docker/dockerfile:1.7
#
# Self-contained image for QueryBridge:
#   - Stage 1 builds the React/Vite frontend → static dist/
#   - Stage 2 fetches the Mathlib build cache and compiles four Lean
#     executables (sqlGenMain, sqlGenError, sqlGenBug2, sqlGenBug3)
#   - Stage 3 is a slim Python runtime with FastAPI, the Lean binaries,
#     and the static frontend mounted at "/"
#
# Build:
#   docker build -t querybridge .
# Run:
#   docker run --rm -p 8000:8000 querybridge
# Then open http://localhost:8000

# ============================================================
# Stage 1 — Frontend build
# ============================================================
FROM node:20-slim AS frontend-build

WORKDIR /app/frontend

# Cache npm install on lockfile only.
COPY frontend/package.json frontend/package-lock.json ./
RUN npm ci

COPY frontend/ ./
RUN npm run build

# ============================================================
# Stage 2 — Lean build (Mathlib + four executables)
# ============================================================
FROM ubuntu:24.04 AS lean-build

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates git build-essential \
    && rm -rf /var/lib/apt/lists/*

# Install elan with the project toolchain (read from lean-toolchain).
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain leanprover/lean4:v4.29.0
ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /build/ProofPilot

# Step 1 — pull dependencies. Done before copying source so changes to
# .lean files don't reinvalidate the dep download layer.
#
# `lake update` exits non-zero because Mathlib's post-update hook attempts
# to fetch the prebuilt-olean cache, and Plausible's main branch wants a
# newer Lean toolchain than Mathlib's v4.29.0 oleans were built against.
# We tolerate that — the dependency *sources* are downloaded successfully
# before the hook runs — then restore the project toolchain to match
# Mathlib's so the subsequent build picks the right elan toolchain.
COPY ProofPilot/lakefile.lean ProofPilot/lean-toolchain ./
RUN lake update || true \
 && cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain

# Step 2 — try to fetch Mathlib's prebuilt oleans (~minutes, vs ~hour from
# source). Tolerate failure: when the cache binary can't run on this
# host's architecture, lake build falls back to compiling Mathlib bits on
# demand, which is slow but reliable.
RUN lake exe cache get || true

# Step 3 — bring in the project's Lean source and build the four exes.
COPY ProofPilot/*.lean ./
RUN lake build sqlGenMain sqlGenError sqlGenBug2 sqlGenBug3

# ============================================================
# Stage 3 — Runtime
# ============================================================
FROM python:3.12-slim AS runtime

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1

# Lean executables link against libgcc_s and libstdc++.
RUN apt-get update && apt-get install -y --no-install-recommends \
        libgcc-s1 libstdc++6 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Backend Python deps first — cached on requirements.txt only.
COPY backend/requirements.txt /app/backend/requirements.txt
RUN pip install --no-cache-dir -r /app/backend/requirements.txt

# Backend source.
COPY backend/ /app/backend/

# Lean binaries — only the four executables, ~125 MB each.
COPY --from=lean-build /build/ProofPilot/.lake/build/bin/sqlGenMain   /app/ProofPilot/.lake/build/bin/sqlGenMain
COPY --from=lean-build /build/ProofPilot/.lake/build/bin/sqlGenError  /app/ProofPilot/.lake/build/bin/sqlGenError
COPY --from=lean-build /build/ProofPilot/.lake/build/bin/sqlGenBug2   /app/ProofPilot/.lake/build/bin/sqlGenBug2
COPY --from=lean-build /build/ProofPilot/.lake/build/bin/sqlGenBug3   /app/ProofPilot/.lake/build/bin/sqlGenBug3

# Static frontend bundle — served by FastAPI in production (see main.py).
COPY --from=frontend-build /app/frontend/dist /app/frontend/dist

EXPOSE 8000

WORKDIR /app/backend
CMD ["uvicorn", "main:app", "--host", "0.0.0.0", "--port", "8000"]
