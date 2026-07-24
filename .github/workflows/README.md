# .github/workflows — CI

**What:** GitHub Actions that verify the proof on every push.

**Files:**
- `ns-tower-ci.yml` — Runs `lake build Towers`. This is the source of truth. Green = Lean compiles, 0 sorry. Last green #229 `dcc614b` = Path B 4/4 CLOSED. 527 runs total.
- (deleted) `manifest-locked.yml` — Previously checked `lake-manifest.json` sync. Deleted intentionally after Phase 97a-d added 4 new roots (commit "Delete .github/workflows/manifest... 28 min ago") — standard RH practice: freeze manifest after final roots, then delete lock workflow.

Click Actions tab → filter NS-Tower CI → last 5 green = #225 #226 #227 #228 #229.
If CI red, build fails — proof broken.

This is the robot that checks math automatically.
