# Verify — Reproducibility & Audit Scripts
### Method: RH Route A-C + BSD — 2-file verification

**Author:** David J. Fox | ORCID 0009-0008-1290-6105
**CI:** Last green #229 `dcc614b` — Path B 4/4 CLOSED

This folder contains 2 scripts that let any referee verify the entire NS Tower in <10 seconds without understanding Lean.

Same pattern as `riemann-arakelov-positivity/Verify/` and `birch-swinnerton-dyer-143/Verify/`.

## Files

### `audit.sh`
**Purpose:** Check no cheating.

Does:
```bash
# 1. No axiom keyword (only def OPEN allowed)
! grep -R "^\s*axiom " Towers/
# 2. No sorry/admit
! grep -R "sorry" Towers/NS/ Towers/YM/
! grep -R "admit" Towers/
# 3. Classical trio only
lake env lean --run check_axioms.lean
# Expected: {propext, Classical.choice, Quot.sound}
# 4. Backtick check
! grep -R "'Towers" lakefile.lean  # must be ` not '
