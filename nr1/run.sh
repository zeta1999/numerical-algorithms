#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_DIR="$SCRIPT_DIR/lean"
FSTAR_DIR="$SCRIPT_DIR/fstar"

echo "========================================"
echo " LU Decomposition - Build & Test Suite"
echo "========================================"

# ========================================
# LEAN4
# ========================================
echo ""
echo "----------------------------------------"
echo " Lean4 Implementation"
echo "----------------------------------------"

cd "$LEAN_DIR"

# Step 1: Fetch dependencies (if needed)
echo ""
echo "[1/5] Fetching dependencies..."
if [ ! -d ".lake/packages/mathlib" ]; then
    lake update
else
    echo "  Dependencies already present, skipping."
fi

# Step 2: Build library
echo ""
echo "[2/5] Building library..."
lake build LUDecomp
echo "  ✓ Library built successfully"

# Step 3: Run unit tests
echo ""
echo "[3/5] Running unit tests..."
lake build test
lake exe test
echo ""

# Step 4: Run fuzz tests
echo ""
echo "[4/5] Running fuzz tests..."
lake build fuzz
lake exe fuzz
echo ""

# Step 5: Run sensitivity analysis
echo ""
echo "[5/5] Running sensitivity analysis..."
lake build sensitivity
lake exe sensitivity
echo ""

echo "  ✓ Lean4 — all steps completed"

# ========================================
# F*
# ========================================
echo ""
echo "----------------------------------------"
echo " F* Implementation"
echo "----------------------------------------"

cd "$FSTAR_DIR"

if command -v fstar.exe &> /dev/null; then
    echo ""
    echo "[1/1] Verifying F* modules..."
    make verify
    echo "  ✓ F* — all modules verified"
else
    echo ""
    echo "  ⚠ fstar.exe not found — skipping F* verification"
    echo "  To install: opam install fstar"
    echo ""
    echo "  F* source files present:"
    for f in src/*.fst; do
        echo "    - $f"
    done
fi

echo ""
echo "========================================"
echo " All steps completed successfully"
echo "========================================"
