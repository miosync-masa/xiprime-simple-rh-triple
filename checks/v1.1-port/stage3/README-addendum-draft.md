<!-- Draft for the README of v1.1. Not yet merged into README.md. -->

## The version without the RH hypothesis (v1.1)

`lean/RHTripleIntegration/Unconditional.lean` states the two final theorems with no hypothesis:

```lean
theorem xiPrime_simple_proportion_c20_unconditional :
    1 - c20/3 ≤ liminf (fun T => (Zeta23.XiPrime.N0simple 0 T : ℝ) /
      (Zeta23.XiPrime.Ncount 0 T : ℝ)) atTop
```

and the same with `0.9742` on the left. Here `c20 = 77223/1000000`, so the bound is
`1 - c20/3 = 974259/1000000`: at least 97.42% of the zeros of ξ′ are simple and on the critical
line, in the sense of this liminf.

The proof is one line: the RH-conditional theorem of v1.0 applied to
`riemannHypothesis : RiemannHypothesis`, taken from the compiled release of the Lean proof of
RH by L. Alpöge (https://proofsandreasons.io/rh-oleans.html). `#print axioms` gives
`propext`, `Classical.choice`, `Quot.sound`.

This file is not part of the default build: it needs the release (14 archives, 31.92 GiB;
about 88 GB extracted) on `LEAN_PATH`, Lean v4.33.1 and the release's own Mathlib
(`0df444a3…`). The steps and hashes are in `checks/v1.1-port/stage3/`.

## Scope of trust

- Lean does not re-check a compiled object when it is imported. Our compilation checked the
  two new theorems only. `riemannHypothesis` is used as the release provides it.
- We verified that the files we used are the published ones: all 14 archives and all 175,187
  module objects match the release's SHA-256 lists, and `Main.olean`
  (`9146dfb4…ddf796ad`) matches the value recorded on A. Sutherland's verification page
  (https://math.mit.edu/~drew/grh/).
- We did **not** re-verify the release. For that, see the release's own page and the
  independent checks reported on Sutherland's page.
- A second pass through the kernel (replay of the stored declarations, with `leanchecker` of
  Lean 4.33.1 and, for 7 modules, with `tools/ReplayOne.lean`) passed for all 90 modules of
  this repository and all 317 modules of AF. This is the same kernel again, not an independent
  checker. comparator and independent kernels were not run by us.
- Everything else in this repository (89 modules) and AF (317 modules) was compiled from source
  against the release's Mathlib, with no `sorry` and no error.
- The RH-conditional theorems of v1.0 remain in the repository unchanged and do not depend on
  the release.
