/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.SemCheck

/-! # From the Boolean gate to an inequality between real integrals (degree-independent)

`gate_real`: if `IntCheck.gate D N P gn gd = true` and the Boolean degree condition `degOK`
holds, then for `Pt = scaleTab D 0 P`
`(4·sqR (S2 Pt) + 6·J3R Pt − 6·J4R Pt)·gd ≤ (gn − 2·gd)·(sqR (S0 Pt))²` and `sqR (S0 Pt) ≠ 0`,
i.e. `2 + (4·I₂ + 6·J₃ − 6·J₄)/I₀² ≤ gn/gd` for the iterated real integrals. -/

namespace XiPrime8845.Triple.IntCheck.Sem
open Pack

def degOK (D N : ℕ) (P : List (List Int)) : Bool :=
  decide (degQ (scaleTab D 0 P) + 3 ≤ N)
    && decide (dm (deg0 (scaleTab D 0 P)) (deg0 (scaleTab D 0 P)) + 1 ≤ N)
    && decide (deg0 (scaleTab D 0 P) + 1 ≤ N)

theorem lcmUpTo_pos : ∀ N, 0 < lcmUpTo N
  | 0 => Nat.one_pos
  | N + 1 => Nat.lcm_pos (lcmUpTo_pos N) (Nat.succ_pos N)

theorem gate_real {D N : ℕ} {P : List (List Int)} {gn gd : Int}
    (hdeg : degOK D N P = true) (hg : IntCheck.gate D N P gn gd = true) :
    sqR (S0 (scaleTab D 0 P)) ≠ 0 ∧
    (4 * sqR (S2 (scaleTab D 0 P)) + 6 * J3R (scaleTab D 0 P) - 6 * J4R (scaleTab D 0 P)) * gd
      ≤ ((gn : ℝ) - 2 * gd) * sqR (S0 (scaleTab D 0 P)) ^ 2 := by
  simp only [degOK, Bool.and_eq_true, decide_eq_true_eq] at hdeg
  obtain ⟨⟨h4, h2⟩, h0⟩ := hdeg
  have g : 0 < i0 (lcmUpTo N : ℤ) (scaleTab D 0 P) ^ 2 ∧
      (4 * i2 (lcmUpTo N : ℤ) (scaleTab D 0 P) * (lcmUpTo N : ℤ) ^ 2
        + 6 * j3 (lcmUpTo N : ℤ) (scaleTab D 0 P) * (lcmUpTo N : ℤ)
        - 6 * j4 (lcmUpTo N : ℤ) (scaleTab D 0 P)) * gd
      ≤ (gn - 2 * gd) * i0 (lcmUpTo N : ℤ) (scaleTab D 0 P) ^ 2 := by
    simp only [IntCheck.gate, IntCheck.numDen, Bool.and_eq_true] at hg
    exact ⟨of_decide_eq_true hg.1, of_decide_eq_true hg.2⟩
  have g1 : (0 : ℝ) < ((i0 (lcmUpTo N : ℤ) (scaleTab D 0 P) : ℤ) : ℝ) ^ 2 := by exact_mod_cast g.1
  have g2 : (4 * ((i2 (lcmUpTo N : ℤ) (scaleTab D 0 P) : ℤ) : ℝ) * (lcmUpTo N : ℝ) ^ 2
        + 6 * ((j3 (lcmUpTo N : ℤ) (scaleTab D 0 P) : ℤ) : ℝ) * (lcmUpTo N : ℝ)
        - 6 * ((j4 (lcmUpTo N : ℤ) (scaleTab D 0 P) : ℤ) : ℝ)) * (gd : ℝ)
      ≤ ((gn : ℝ) - 2 * gd) * ((i0 (lcmUpTo N : ℤ) (scaleTab D 0 P) : ℤ) : ℝ) ^ 2 := by
    exact_mod_cast g.2
  rw [i0_real _ h0] at g1 g2
  rw [i2_real _ h2, j3_real _ h4, j4_real _ h4] at g2
  have hL : (0 : ℝ) < (lcmUpTo N : ℝ) := by exact_mod_cast lcmUpTo_pos N
  have hL4 : (0 : ℝ) < (lcmUpTo N : ℝ) ^ 4 := by positivity
  refine ⟨?_, ?_⟩
  · intro h; rw [h] at g1; simp at g1
  · have : (lcmUpTo N : ℝ) ^ 4 * ((4 * sqR (S2 (scaleTab D 0 P)) + 6 * J3R (scaleTab D 0 P)
          - 6 * J4R (scaleTab D 0 P)) * gd)
        ≤ (lcmUpTo N : ℝ) ^ 4 * (((gn : ℝ) - 2 * gd) * sqR (S0 (scaleTab D 0 P)) ^ 2) := by
      calc _ = (4 * ((lcmUpTo N : ℝ) ^ 2 * sqR (S2 (scaleTab D 0 P))) * (lcmUpTo N : ℝ) ^ 2
              + 6 * ((lcmUpTo N : ℝ) ^ 3 * J3R (scaleTab D 0 P)) * (lcmUpTo N : ℝ)
              - 6 * ((lcmUpTo N : ℝ) ^ 4 * J4R (scaleTab D 0 P))) * (gd : ℝ) := by ring
        _ ≤ _ := g2
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hL4

end XiPrime8845.Triple.IntCheck.Sem
#print axioms XiPrime8845.Triple.IntCheck.Sem.gate_real
