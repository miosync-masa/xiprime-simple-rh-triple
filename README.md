# Simple critical-line zeros of the Riemann xi derivative under RH: beyond 97.42%

Lean 4 proof that, assuming the Riemann hypothesis, more than 97.42% of the zeros of $\xi'$ are simple and lie on the critical line.

Author: **Masamichi Iizumi** · Miosync, Inc., Tokyo, Japan · ORCID [0009-0007-0755-403X](https://orcid.org/0009-0007-0755-403X)

DOI: [TODO: reserved Zenodo DOI]

## The theorem

[`xiPrime_simple_proportion_c20`](lean/RHTripleIntegration/SimpleProportion.lean):

```lean
xiPrime_simple_proportion_c20 : RiemannHypothesis →
  1 - c20 / 3 ≤ liminf (fun T => ↑(XiPrime.N0simple 0 T) / ↑(XiPrime.Ncount 0 T)) atTop
```

with `c20 = 77223/1000000`, so that

$$
\liminf_{T\to\infty}\frac{N^{s}_{0,\xi'}(T)}{N_{\xi'}(T)}\ \ge\ 1-\frac{c_{20}}{3}=\frac{974259}{1000000}=0.974259 .
$$

The companion `xiPrime_simple_proportion_ge_9742` states `0.9742 ≤ liminf …`. Both counts are the actual $\xi'$ counts of the pinned Alpöge–Furman (AF) library: the denominator counts all zeros of $\xi'$ with multiplicity, the numerator counts simple zeros on the critical line.

Both theorems print exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The only hypothesis in the type is `RiemannHypothesis`, Mathlib's definition, which is not redefined anywhere in this repository or in the pinned AF library. **The bound is 0.974259. It is not stated as ≥ 97.43%.**

## About RH

This repository does not prove RH. The statement of `RiemannHypothesis` is textually identical at our Mathlib pin (`51e6992e…`) and at the pin of the Lean proof of RH by L. Alpöge with Claude ([Deicyde/riemann-hypothesis](https://github.com/Deicyde/riemann-hypothesis), `Main.lean`, commit `40e56bab…`; Lean v4.33.1, Mathlib `0df444a3…`), which is the subject of the joint statement [Lean verification of the Riemann Hypothesis](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/). Supplying that theorem for the hypothesis removes it. A build combining both libraries in a single environment is not part of this release.

## Proof outline

| Step | Content | Main declaration |
|---|---|---|
| 1 | Under RH, zeros of $\xi'$ = simple zeros on the line + $\sum_{m_\rho\ge3}(m_\rho-1)$ over zeros of $\zeta$ | `Ncount_eq` |
| 2 | Smoothed three-point correlation of $\zeta$ for distinct zero slots, Fourier support in the hexagon $\lvert u\rvert+\lvert v\rvert+\lvert u+v\rvert<2$ | `zeta_smoothed_distinct_triple_main_count` |
| 3 | Collision extraction for $M_3=\sum m(m-1)(m-2)$, removal of height smoothing, dyadic summation | `FactorialMoment`, `HeightMajorant`, `CertificateLimit` |
| 4 | Degree-20 test function of Gonçalves–de Laat–Leijenhorst, kernel-checked: $\nu_3^F(\Phi_0)/\mathrm{mass}(\Phi_0)\le c_{20}$ | `P20_nu3` |
| 5 | Shrink-and-mollify family with nonnegative inverse transform; the bound passes to the limit | `CertificateSmoothing`, `planeInverse_real_autocorrelation` |
| 6 | $3(m-1)\le m(m-1)(m-2)$ for $m\ge3$, inserted into the bridge | `simple_proportion_of_highZeros_bound` |

Step 2 is the $\zeta$ case of the Hejhal / Rudnick–Sarnak three-level correlation, proved from AF's Weil explicit formula with the actual Gamma kernel, including the two-point marginals required by the inclusion–exclusion.

## Verification

Rebuild record: [`checks/clean-rebuild/`](checks/clean-rebuild/). Reproduce with `python3 tools/closure.py` and `python3 tools/build.py <built AF checkout> <empty directory>`.

| Item | Result |
|---|---|
| Scope | every Lean file of this repository (= the import closure of the final theorem), rebuilt from an empty output directory |
| Modules | 89/89 succeeded (RHTriple 61, TripleCorrelation 23, RHTripleIntegration 4, RHBridge 1) |
| Errors / `sorryAx` | 0 / 0 |
| Forbidden constructs in the closure | no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by` |
| Source composite SHA-256 | `ae796aa642530c711f4a315706a462b09d9618f8bdcfc68ae4d6d20f65b66979` |
| `.olean` composite SHA-256 | `67771794ab64256a3b40460c2ef03c1c7d243c5998d5599bab4c60fa1017cd6f` |
| Provenance | sources byte-identical to branch `rh-ximain-integration` of `xiprime-simple-local-energy` at `ef32d75` (same source composite hash as its audit, [`checks/source-branch-audit/`](checks/source-branch-audit/)) |

The rebuild used the existing build of the pinned AF library (and its Mathlib); it is not a rebuild of AF or Mathlib. Five pairs of definitions (`nu3F`, `nu3Mass`/`mass`, `nu3Kernel`/`K`, `lineInt`, `hexGauge`/`hexSum`) exist twice, once in `RHTriple` and once in `TripleCorrelation`, and are checked equal by `rfl` in `checks/clean-rebuild/check.lean`.

## Pins

- Lean `v4.33.0-rc2`; Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`
- AF library `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` (unmodified)

## Not included or not claimed

- No proof of RH.
- No degree-50 certificate: it has never been kernel-checked and is not part of this repository.
- No claim that the constant is optimal, or that the deduction is new in the literature: it is a short consequence of known theorems. The contribution is the end-to-end kernel-checked proof.

## Related repositories

This repository contains only the import closure of the final theorem. The unconditional 87.328% simple-zero theorem is a separate repository (`xiprime-simple-local-energy`, tag `v1.0.0`, doi:[10.5281/zenodo.24210376](https://doi.org/10.5281/zenodo.24210376)); none of its files is contained in or needed by this one. The related 88.45% multiplicity-counting project is doi:[10.5281/zenodo.24101490](https://doi.org/10.5281/zenodo.24101490).

## References and attribution

- L. Alpöge, with Claude, Lean development of the Riemann hypothesis (2026), <https://github.com/Deicyde/riemann-hypothesis>; joint statement <https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>.
- L. Alpöge, R. Furman, arXiv:2608.13637v2, and the AF Lean library (Anthropic).
- Z. Rudnick, P. Sarnak, Duke Math. J. 81 (1996).
- F. Gonçalves, D. de Laat, N. Leijenhorst, arXiv:2303.01095v2, and its ancillary code and data (integration regions and polynomial data used in `TripleCorrelation/`).
- D. W. Farmer, S. M. Gonek, arXiv:0803.0425.

See [LICENSE](LICENSE) and [NOTICE](NOTICE). New files are © 2026 Masamichi Iizumi (Miosync, Inc.), Apache-2.0. AI tools (Claude, ChatGPT/Codex) assisted development and verification; responsibility for all claims rests with the author.
