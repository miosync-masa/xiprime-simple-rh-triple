# v1.1 stage 2: port to the target pin and audit

Date: 2026-11-25. Branch `v1.1-port-4331`. Audited sources: commit `592e3a5`.

## The change
| File | Change |
|---|---|
| `lean/RHTriple/PolarGate.lean` | 1 line: `Asymptotics.IsLittleO.sum` → `Asymptotics.IsLittleO.fun_sum` |
| `lean/RHTriple/TriplePrimeGate.lean` | 3 lines: the same replacement |
| `lean-toolchain` | `leanprover/lean4:v4.33.0-rc2` → `leanprover/lean4:v4.33.1` |

No statement, no definition and no number of the certificate was changed; the other 87 Lean
files are byte-identical to `main` (`fa0578a`). The README on this branch still describes the
v1.0 pins and is to be revised in stage 3.

## Environment
- Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (arm64 macOS binary).
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and the seven other dependency revisions of
  the release README (identical, see stage 1).
- AF: the sources of `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` with three pin files changed
  (`lean-toolchain` SHA-256 `3aac669c…f5db71`, `lakefile.toml` `703b84e2…929826b`,
  `lake-manifest.json` `c497718a…fd1b59bc`). `diff -r` against the pinned checkout shows no
  other difference. Its build (made on 2026-11-22 with Mathlib's official cache) was confirmed
  up to date by `lake build Zeta23` (9019 jobs replayed, none rebuilt) and was not rebuilt.
  The pinned AF checkout itself was not touched.

## Clean rebuild (from an empty output directory)
- 89/89 modules succeeded; 0 errors; 0 occurrences of `sorryAx`; 20 linter warnings.
- Wall 223.2 s with 3 workers; `D20Pack` (kernel evaluation of the certificate) included.
- Combined SHA-256 of the sources `0fc6ba0b12e136ebff1e81d1c3a2766fd31ffcd28edb5a433b2cd980a90ea72c`;
  of the `.olean` files `f05b785bd741472f5b4e7a345ec0528b9b33307ba3f86f57d3ba40c7798e5351`
  (the stage-1 trial with the same sources in another directory gave a different `.olean` hash;
  object files are not reproducible across directories, as Sutherland's page also notes).
- Per-module values: `build.json`.

## Final theorems on the target pin (`check.out`)
```
xiPrime_simple_proportion_c20 : RiemannHypothesis →
  1 - c20 / 3 ≤ liminf (fun T => ↑(Zeta23.XiPrime.N0simple 0 T) / ↑(Zeta23.XiPrime.Ncount 0 T)) atTop
xiPrime_simple_proportion_ge_9742 : RiemannHypothesis →
  0.9742 ≤ liminf (the same ratio) atTop
```
Same types as on the old pin. `#print axioms`: `[propext, Classical.choice, Quot.sound]` for both.
The five duplicated definitions are equal by `rfl`; `1 − c20/3 = 974259/1000000`.
No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `extern` in
the 89 files.

## Not done in this stage
- Nothing of the RH release has been downloaded or imported; `RiemannHypothesis` is still a
  hypothesis of both theorems.
- AF was not rebuilt from scratch on the target pin today.
- The d = 50 certificate is not part of the repository and was not ported.
