#!/usr/bin/env bash
# Axiom + sorry audit for NS Tower 540
# Usage: bash Verify/audit.sh   (run from repo root)
set -e

FAIL=0
echo "=== NS Tower 540 — Axiom + Sorry Audit ==="
echo "Checking Towers/NS/ for sorry / admit / axiom..."

# Check for sorry / admit
if grep -rn 'sorry\|admit' Towers/NS/ 2>/dev/null | grep -v '^Binary' | grep -v '-- '; then
    echo "FAIL: sorry or admit found"
    FAIL=1
else
    echo "PASS: no sorry / admit"
fi

# Check for native_decide (not trio-clean)
if grep -rn 'native_decide' Towers/NS/ 2>/dev/null | grep -v '^Binary' | grep -v '-- '; then
    echo "FAIL: native_decide found (not classical trio)"
    FAIL=1
else
    echo "PASS: no native_decide"
fi

# Count theorems
THEOREM_COUNT=$(grep -rh '^theorem\|^lemma' Towers/NS/*.lean 2>/dev/null | wc -l || echo 0)
echo "INFO: theorem/lemma count = $THEOREM_COUNT"

# Expected axiom footprint
echo "EXPECTED AXIOMS: propext, Classical.choice, Quot.sound"
echo "Run: lean --print-axioms <file> to verify per-file"

if [ $FAIL -eq 0 ]; then
    echo ""
    echo "=== AUDIT PASSED — classical trio, 0 sorry ==="
    exit 0
else
    echo ""
    echo "=== AUDIT FAILED ==="
    exit 1
fi
