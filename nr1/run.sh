#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_DIR="$SCRIPT_DIR/lean"

cd "$LEAN_DIR"

echo "========================================"
echo " LU Decomposition - Build & Test Suite"
echo "========================================"
echo ""

# Step 1: Fetch dependencies (if needed)
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

echo "========================================"
echo " All steps completed successfully"
echo "========================================"
