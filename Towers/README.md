### 3. `Towers/README.md`

```md
# Towers — All Lean Proofs

Contains two sub-towers:

- `Towers/NS/` — Navier-Stokes Clay Tower — Main proof. 80+ Lean files, Path A 101-108 + Path B 97a-d.
- `Towers/YM/` — Yang-Mills walls 261,263,264 — Shared with `yang-mills-gap` repo. Uses same H4 vertices as NS 120-cell.

**Dependency:** Towers is declared in `lakefile.lean` as `lean_lib Towers` with 22 roots. Building `lake build Towers` builds everything.

**Structure:**
Towers/
  NS/ — NS M6 proof (see Towers/NS/README.md for file table)
  YM/ — YM mass gap auxiliary (see Towers/YM/README.md)
**For referee:** No cycles allowed. Lean checks acyclicity.
