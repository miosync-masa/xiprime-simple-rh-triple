<!-- Draft for the README of v1.1 (revision 2, 2026-11-25). Not yet merged into README.md. -->

## Without the RH hypothesis (v1.1)

**What Lean checked in this version.** Lean checked, from the sources of this repository and of
the AF library and against compiled Mathlib, the implication "RH implies the bound below", and
the one line that applies it to `riemannHypothesis` from the compiled release of the Lean proof
of RH by L. Alpöge (https://proofsandreasons.io/rh-oleans.html). Lean did not re-check the proof
of RH itself here.

`lean/RHTripleIntegration/Unconditional.lean` states:

```lean
theorem xiPrime_simple_proportion_c20_unconditional :
    1 - c20/3 ≤ liminf (fun T => (Zeta23.XiPrime.N0simple 0 T : ℝ) /
      (Zeta23.XiPrime.Ncount 0 T : ℝ)) atTop
```

and the same with `0.9742` on the left, where `c20 = 77223/1000000` and
`1 - c20/3 = 974259/1000000`. The denominator counts all zeros of ξ′ with multiplicity; the
numerator counts simple zeros on the critical line. In the sense of this liminf, at least 97.42%
of the zeros of ξ′ are simple and on the critical line. The bound is not stated as ≥ 97.43%.

The type of the theorem has no hypotheses. Its proof is the RH-conditional theorem of v1.0
applied to `riemannHypothesis`. `#print axioms` gives `propext`, `Classical.choice`,
`Quot.sound`.

### Build

This file is not part of the default build. It needs:

- Lean v4.33.1 and the release's own Mathlib (`0df444a3…`);
- the release on `LEAN_PATH` (14 archives, 31.92 GiB; 93.94 GiB extracted, of which 88.09 GiB
  are the release's modules and 5.85 GiB its dependencies);
- AF at `3635e748`, sources unmodified, compiled with that Lean against that Mathlib. AF's own
  pin files name an older toolchain and Mathlib; they were left as they are and not used, since
  the modules were compiled with `lean` directly (`tools/build_direct.py`).

In v1.0 the pins were Lean v4.33.0-rc2 and AF's own Mathlib. For v1.1, four lines in two files
of this repository changed (`Asymptotics.IsLittleO.sum` → `Asymptotics.IsLittleO.fun_sum`); no
statement, definition or certificate number changed.

Steps and hashes: `checks/v1.1-port/stage3/`.

## Scope of trust

- Lean does not re-check a compiled object when it is imported. Our compilation of
  `Unconditional.lean` checked the two new theorems only; `riemannHypothesis` is used as the
  release provides it.
- We checked that the files we used are the published ones: all 14 archives and all 175,187
  module objects match the release's SHA-256 lists, and `Main.olean` (`9146dfb4…ddf796ad`)
  matches the value recorded on A. Sutherland's verification page
  (https://math.mit.edu/~drew/grh/).
- We did **not** re-verify the release, and we did not rerun the checks reported on Sutherland's
  page.
- All 89 modules of this repository, `Unconditional.lean`, and all 317 modules of AF were
  compiled from source against the release's Mathlib, with no `sorry` and no error. Mathlib
  itself was not compiled by us; its objects are those shipped in the release (the 52,160 object
  files we compared are byte-identical to the ones from Mathlib's official cache).
- A second pass through the kernel (replay of the stored declarations with `leanchecker` of
  Lean 4.33.1) passed for all 90 modules of this repository and all 317 modules of AF. This is
  the same kernel again, not an independent checker. We did not run comparator or an
  independent kernel.
- `tools/ReplayOne.lean` is a checking tool that copies `replayFromImports` from `leanchecker`
  and contains `unsafe def`. It is outside the closure of the theorems: no module under `lean/`
  imports anything from `tools/`.
- The RH-conditional theorems of v1.0 remain unchanged and do not depend on the release.
