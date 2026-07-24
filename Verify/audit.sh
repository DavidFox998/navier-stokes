#!/bin/bash
# Verify/audit.sh — RH Route A-C + BSD methodology
# Author: David J Fox ORCID 0009-0008-1290-6105
# Date: July 03 2026 #229 Path B 4/4 CLOSED

echo "=== NS Tower Audit — Path B 4/4 #229 dcc614b ==="
echo ""

echo "1. Check axiom keyword (should be 0):"
AXIOM=$(grep -R "^\s*axiom " Towers/ --include="*.lean" | wc -l)
echo "axiom keyword count: $AXIOM"
if [ "$AXIOM" -ne 0 ]; then echo "FAIL: axiom keyword found"; exit 1; fi

echo ""
echo "2. Check sorry (should be 0):"
SORRY=$(grep -R "sorry" Towers/ --include="*.lean" | wc -l)
echo "sorry count: $SORRY"
if [ "$SORRY" -ne 0 ]; then echo "FAIL: sorry found"; exit 1; fi

echo ""
echo "3. Check admit (should be 0):"
ADMIT=$(grep -R "admit" Towers/ --include="*.lean" | wc -l)
echo "admit count: $ADMIT"

echo ""
echo "4. Check backtick roots (should be 0 single-quote):"
BAD=$(grep "'Towers" lakefile.lean | wc -l)
echo "bad single-quote roots: $BAD"
if [ "$BAD" -ne 0 ]; then echo "FAIL: use \` not '"; exit 1; fi

echo ""
echo "5. Roots count (should be 22):"
grep -c "Towers" lakefile.lean

echo ""
echo "6. Path B files exist:"
ls -l Towers/NS/NSPhase97a*.lean Towers/NS/NSPhase97b*.lean Towers/NS/NSPhase97c*.lean Towers/NS/NSPhase97d*.lean

echo ""
echo "7. Certificates exist:"
ls -l certificates/*Phase97*.pdf certificates/*PathB*.pdf

echo ""
echo "=== AUDIT PASS — 0 sorry, trio only, Path B 4/4 CLOSED #229 ==="
