# RHBridge

`MultiplicityBridge.lean` — every theorem that uses the Riemann Hypothesis takes
`hRH : RiemannHypothesis` (Mathlib's statement) as an explicit argument.

| Theorem | Uses `hRH` | Statement |
|---|---|---|
| `re_eq_half_of_xiDeriv_eq_zero` | yes | ξ′(s) = 0, ξ(s) ≠ 0 ⇒ Re s = 1/2 |
| `xiDerivMult_eq_one` | yes | ξ′(s) = 0, ξ(s) ≠ 0 ⇒ the zero of ξ′ is simple |
| `xiDerivMult_add_one` | no | at a nontrivial zero of ζ: ord ξ′ + 1 = ord ζ |
| `Ncount_eq` | yes | N_{ξ′}(T₁,T₂) = N⁰ˢ_{ξ′}(T₁,T₂) + Σ_{m_ρ ≥ 3} (m_ρ − 1) |
| `Ncount_sub_N0simple_le` | yes | inequality form |
| `eventually_zetaCount_le` | no | N_ζ(T,2T) ≤ (1+δ)·N_{ξ′}(T,2T) eventually |
| `simple_proportion_of_highZeros_bound` | yes | Σ_{m≥3}(m−1) ≤ c·N_ζ eventually ⇒ (1−c−ε)·N_{ξ′} ≤ N⁰ˢ_{ξ′} eventually |

Attribution: the proof of `eventually_zetaCount_le` mirrors
`Zeta23.XiPrime.eventually_zetaCount_le_Ncount` (AF, `Zeta23/XiPrime/Final.lean`,
Copyright (c) 2026 Anthropic, PBC, Apache-2.0) with the two configurations exchanged; see `NOTICE`.
