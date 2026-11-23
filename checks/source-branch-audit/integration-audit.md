# Audit record of the integration branch

Date: 2026-11-23. Branch `rh-ximain-integration`. Audited sources: commit `56e4ff9`
(= `a730e56` plus copyright headers on the 95 new Lean files and status comments on the two
d = 50 files; no declaration changed: for 93 files the old text is a suffix of the new text,
the other two are `D50Bound.lean` and `D50Pack.lean`). This record was added in the commit
after `56e4ff9`.

Pinned upstream AF: `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` (unmodified checkout, its
existing build products were used). Lean `v4.33.0-rc2`, Mathlib `51e6992e…`.

## Result
```
xiPrime_simple_proportion_c20 : RiemannHypothesis →
  1 - c20 / 3 ≤ liminf (fun T => ↑(Zeta23.XiPrime.N0simple 0 T) / ↑(Zeta23.XiPrime.Ncount 0 T)) atTop
xiPrime_simple_proportion_ge_9742 : RiemannHypothesis →
  0.9742 ≤ liminf (the same ratio) atTop
c20 := 77223 / 1000000,   1 − c20/3 = 974259/1000000   (checked in `check.lean`)
```
Wording: "at least `1 − c₂₀/3`", "0.974259", "at least 97.42%". Not 97.43%.

## 1. Clean rebuild
- Scope: the import closure of the final theorems, 89 modules (RHTriple 61,
  TripleCorrelation 23, RHTripleIntegration 4, RHBridge 1), compiled into an empty directory
  with `closure.py` and `build.py` (3 workers).
- 89/89 succeeded; 0 errors; 0 occurrences of `sorryAx`; 20 linter warnings in 13 files.
- Wall time 172.2 s; sum of module times 432.8 s.
- Combined SHA-256 of the sources `ae796aa6…65b66979`, of the `.olean` files `265b5417…1bb49d8a`;
  per-module values in `build.json`.
- New files outside the closure: `P10`, `D10Pack`, `D20Real`, `P50` were compiled in addition
  (no errors). `D50Bound`, `D50Pack` were not compiled (see 6).
- Not rebuilt here: the v1.0.0 part of the repository (no difference from `612d6a1` outside the
  new directories) and the upstream AF library.
- The run before the headers were added (commit `a730e56`, 89/89, 0 errors, 0 `sorryAx`,
  159.0 s) is kept as `build-before-headers-a730e56.raw.json`.

## 2, 3. Axioms and hypotheses
- `#print axioms` of both theorems: `[propext, Classical.choice, Quot.sound]` (`check.out`).
- The only argument is `RiemannHypothesis`, Mathlib's definition; it is not redefined in the
  89 files or in the pinned AF sources.
- The 89 files contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`,
  `implemented_by`, `extern`.

## 4. Duplicate definitions
- Two sets of definitions remain: `RHTriple.nu3F / nu3Mass / nu3Kernel / lineInt /
  CertificateSmoothing.hexGauge` and `Triple.Nu3.nu3F / mass / K / lineInt / hexSum`.
- All five pairs are equal by `rfl` (`check.lean`). The final theorem relies on this.
- The inverse-transform step uses `planeInverse_real_autocorrelation` (commit `6c52d5f`).
  `PhiPositive.lean` of the certificate branch (`318b494`) is not in this branch; the merged
  certificate commit is `1037f5a`.

## 5. Copyright headers
- 651 tracked `.lean` files; 95 are new relative to `612d6a1`.
- The 95 new files had no copyright line. They now start with
  "Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.) … Apache License, Version 2.0; see
  LICENSE and NOTICE."
- Additional attribution: `RHBridge/MultiplicityBridge.lean` (one proof mirrors AF's
  `eventually_zetaCount_le_Ncount`); `TripleCorrelation/Checker.lean`, `CheckerInt.lean`,
  `Generic.lean` (integration regions transcribed from the ancillary Julia code of
  Gonçalves–de Laat–Leijenhorst, arXiv:2303.01095v2); `P10.lean`, `P20.lean`, `P50.lean`
  (polynomial data derived from the same ancillary files).
- No new file named OpenAI or Anthropic as copyright holder. The 36 inherited files with an
  Anthropic notice (`lean/PositiveAF`, some `lean/LocalEnergy*`) are unchanged.
- `NOTICE` does not yet mention arXiv:2303.01095v2.

## 6. The d = 50 files
- `TripleCorrelation/D50Bound.lean` and `D50Pack.lean` are not in the import closure of the
  final theorems (`D50Pack` imports `D50Bound`; nothing else imports either).
- They were kept in the tree and marked "UNCHECKED and UNUSED" in their own header comments
  and in `lean/TripleCorrelation/README.md`. They have never been compiled successfully.
