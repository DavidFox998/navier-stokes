#!/usr/bin/env bash
# Theorem count per file for NS Tower 540
echo "=== NS Tower 540 — Theorem Count ==="
for f in Towers/NS/*.lean; do
    name=$(basename "$f")
    ct=$(grep -c '^theorem\|^lemma' "$f" 2>/dev/null || echo 0)
    printf "  %-35s %3d\n" "$name" "$ct"
done
echo ""
TOTAL=$(grep -rh '^theorem\|^lemma' Towers/NS/*.lean 2>/dev/null | wc -l || echo 0)
echo "  TOTAL: $TOTAL theorems/lemmas"
echo ""
echo "  Open Clay gates: 3"
echo "  (NS_AubinLions_OPEN, NS_NonlinearWeakForm_OPEN, NS_GlobalContinuation_OPEN)"
echo "  Newly closed (2026-06-29): Energy.integration_by_parts"
