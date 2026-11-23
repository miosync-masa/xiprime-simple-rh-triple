# Clean rebuild of this repository

Date: 2026-11-23. Machine: macOS arm64, 24 GB.

- Scope: all 89 Lean files of the repository (`order.json`; RHTriple 61, TripleCorrelation 23,
  RHTripleIntegration 4, RHBridge 1), which is exactly the import closure of
  `RHTripleIntegration.SimpleProportion`. Compiled into an empty directory with
  `tools/closure.py` and `tools/build.py` (3 workers).
- Upstream: AF checkout at `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` with 0 modified files,
  toolchain `leanprover/lean4:v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.
  The existing build of AF and Mathlib was used; they were not rebuilt.
- Result: 89/89 modules succeeded, 0 errors,
  0 occurrences of `sorryAx`, 20 linter warnings.
- Time: wall 154.8 s, sum of module times 394.5 s.
- Combined SHA-256 of the sources: `ae796aa642530c711f4a315706a462b09d9618f8bdcfc68ae4d6d20f65b66979`
  (identical to the value in `../source-branch-audit/build.json`: the sources are byte-identical
  to branch `rh-ximain-integration` of `xiprime-simple-local-energy` at `ef32d75`; only the four
  `RHTripleIntegration` files moved from `integration/lean/` to `lean/`).
- Combined SHA-256 of the `.olean` files: `67771794ab64256a3b40460c2ef03c1c7d243c5998d5599bab4c60fa1017cd6f`
  (differs from the source-branch audit, whose value was `265b5417…1bb49d8a`; the object files
  were produced from a different directory layout, and their reproducibility across layouts was
  not investigated).
- `check.lean` / `check.out`: types of the two final theorems, `#print axioms`
  (`[propext, Classical.choice, Quot.sound]` for both), `rfl` equality of the five duplicated
  definitions, and `1 − c20/3 = 974259/1000000`. No errors.
- The files contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`,
  `implemented_by`, `extern`.
- This record was written before the first commit and therefore does not contain its hash.
