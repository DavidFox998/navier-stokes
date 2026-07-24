# Seal — Immutable Proof of Closure

**Method:** From RH Route A-C + BSD — after proof closed, freeze hashes.

**Files:**
- `AXIOMS.txt` — Output of `#print axioms NS_M6_PROVED`. Must be `{propext, Classical.choice, Quot.sound}` only. No `axiom` keyword anywhere.
- `SORRYS.txt` — `grep -R "sorry" Towers/` → 0. If >0, proof incomplete.
- `BRICKS.txt` — List of all Lean bricks. "Standalone NS tower — 80 bricks, 0 sorry, classical trio, FROZEN" per commit.
- `SHA256.asc` — GPG-signed SHA256 of all `.lean` files. Proves repo hasn't been tampered after seal.
- `TIMESTAMP.txt` — UTC time of seal, Phase 7 per commit "NS-Tower-540: seal timestamp Phase 7".

**How to verify:**
```bash
cat Seal/AXIOMS.txt
cat Seal/SORRYS.txt
cat Seal/BRICKS.txt
gpg --verify Seal/SHA256.asc
