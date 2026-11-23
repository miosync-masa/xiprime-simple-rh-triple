# TripleCorrelation

Kernel-checked re-verification of the degree-20 polynomial certificate of
Gonçalves–de Laat–Leijenhorst, arXiv:2303.01095v2, Section 5, with `c₂₀ = 77223/1000000`.

Main result (`CertFinal.lean`, `P20_nu3`): with `Φ₀ ξ = (Phi0 (pOf P20i) ξ : ℂ)`, the
autocorrelation of `F = P·1_{H₂}` in the original coordinates,

* `Φ₀` is continuous and vanishes outside `|ξ₁|+|ξ₂|+|ξ₁+ξ₂| ≤ 2`;
* `mass Φ₀ ≠ 0` and `(nu3F Φ₀ / mass Φ₀).re ≤ 77223/1000000`.

`cert_nu3` is the degree-independent statement behind it.

| Layer | Files | Content |
|---|---|---|
| checkers | `Checker`, `CheckerInt`, `Generic`, `CheckerPack` | iterated integration of list polynomials; the packed (Kronecker) version evaluated by the kernel |
| packing is lossless | `PackSound` | `boundCheck = true → Pack.numDen = IntCheck.numDen` |
| data and kernel evaluation | `P20`, `D20Pack` | the table and `IntCheck.gate 10 26 P20i 77223 1000000 = true` |
| real semantics | `Sem`, `SemCheck`, `GateReal` | checker integers = powers of `L` times iterated interval integrals |
| regions | `Hexagon`, `HexLink`, `J3Region`, `J4Slice`, `J4Outer`, `J4Final`, `GateRegion` | the pieces are integrals over the hexagon and over intersections of shifted hexagons |
| original coordinates | `Jacobian` | `H₂`, `F`, `Phi0`; `gate_orig` |
| functional | `Nu3Continuity`, `Nu3InclExcl`, `SymReduce`, `Phi0Props`, `CertFinal` | `nu3F`, its inclusion–exclusion form, the 12-fold symmetry reduction, properties of `Phi0`, the final statement |

Boolean side conditions evaluated by the kernel: `boundCheck`, `degOK`, `shapeOK`, `symOK`.

`tools/gdll_exact.py`, `tools/gdll_candidate.py` (python-flint, exact arithmetic over ℚ, outside
Lean) reproduce the published table values from the ancillary data and produce the integer
table of `P20.lean`; `tools/gdll_candidate_d20.json` is their output for d = 20. They are
provenance only: nothing proved in Lean depends on them.

Not in this directory: the readable rational checker `Checker.lean` is not proved equal to
`CheckerInt.lean` (not needed: the chain starts from `CheckerInt`); `Nu3Continuity.lean` contains
a continuity theorem (`ratio_tendsto`, `P20_limit` in `CertFinal`) that the final theorem does
not use; a degree-50 certificate has never been kernel-checked and is not included.
