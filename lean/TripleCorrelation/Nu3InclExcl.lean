/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.Nu3Continuity

/-! # `nu3F` in inclusion–exclusion form

For `Φ` continuous and vanishing outside the closed hexagon `|ξ₁|+|ξ₂|+|ξ₁+ξ₂| ≤ 2`:
`nu3F Φ = Φ(0) + Σ_v ∫₋₁¹ |u| Φ(uv) du − Σ_v ∫₋₁¹ Φ(uv) du − ∫ (|ξ₁|+|ξ₂|+|ξ₁+ξ₂|) Φ + 2 ∫ Φ`.
The first two terms are the all-triples main term, the next two the three pair sums
(`r̂(0) + ∫|α| r̂(α) dα` each), the last one twice the diagonal. -/

open MeasureTheory Filter Topology

namespace XiPrime8845.Triple.Nu3

noncomputable section

def hexSum (ξ : ℝ × ℝ) : ℝ := |ξ.1| + |ξ.2| + |ξ.1 + ξ.2|

def lineAbs (Φ : ℝ × ℝ → ℂ) (ℓ : ℝ → ℝ × ℝ) : ℂ := ∫ u in (-1 : ℝ)..1, ((|u| : ℝ) : ℂ) * Φ (ℓ u)
def linePlain (Φ : ℝ × ℝ → ℂ) (ℓ : ℝ → ℝ × ℝ) : ℂ := ∫ u in (-1 : ℝ)..1, Φ (ℓ u)

theorem lineInt_eq {Φ : ℝ × ℝ → ℂ} {ℓ : ℝ → ℝ × ℝ} (hΦ : Continuous Φ) (hℓ : Continuous ℓ) :
    lineInt Φ ℓ = linePlain Φ ℓ - lineAbs Φ ℓ := by
  have hc := hΦ.comp hℓ
  unfold lineInt linePlain lineAbs
  rw [← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast; ring
  · exact hc.intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun u : ℝ => ((|u| : ℝ) : ℂ) * Φ (ℓ u)).intervalIntegrable _ _

theorem nu3F_eq_inclExcl {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (hsupp : ∀ ξ, Φ ξ ≠ 0 → hexSum ξ ≤ 2) :
    nu3F Φ = Φ (0, 0)
      + (lineAbs Φ (fun u => (u, -u)) + lineAbs Φ (fun u => (u, 0)) + lineAbs Φ (fun u => (0, u)))
      - (linePlain Φ (fun u => (u, -u)) + linePlain Φ (fun u => (u, 0))
          + linePlain Φ (fun u => (0, u)))
      - (∫ ξ : ℝ × ℝ, (hexSum ξ : ℂ) * Φ ξ) + 2 * mass Φ := by
  have hcs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) 2) fun ξ hξ => ?_
    by_contra h
    have h2 := hsupp ξ h
    rw [mem_closedBall_zero_iff, Prod.norm_def, not_le, lt_max_iff] at hξ
    simp only [Real.norm_eq_abs] at hξ
    unfold hexSum at h2
    have h3 := abs_nonneg (ξ.1 + ξ.2)
    have h4 := abs_nonneg ξ.1
    have h5 := abs_nonneg ξ.2
    rcases hξ with hξ | hξ <;> linarith
  have hs : Continuous fun ξ : ℝ × ℝ => (hexSum ξ : ℂ) * Φ ξ := by unfold hexSum; fun_prop
  have i1 : Integrable Φ := hΦ.integrable_of_hasCompactSupport hcs
  have i2 : Integrable fun ξ : ℝ × ℝ => (hexSum ξ : ℂ) * Φ ξ :=
    hs.integrable_of_hasCompactSupport hcs.mul_left
  have e : (∫ ξ : ℝ × ℝ, (K ξ : ℂ) * Φ ξ)
      = mass Φ - (1 / 2) * ∫ ξ : ℝ × ℝ, (hexSum ξ : ℂ) * Φ ξ := by
    unfold mass
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    by_cases h : Φ ξ = 0
    · simp [h]
    · have h2 := hsupp ξ h
      have : K ξ = 1 - hexSum ξ / 2 := by
        unfold K hexSum at *; exact max_eq_right (by linarith)
      simp only [this]; push_cast; ring
  unfold nu3F
  rw [e, lineInt_eq hΦ (by fun_prop), lineInt_eq hΦ (by fun_prop), lineInt_eq hΦ (by fun_prop)]
  ring

end

end XiPrime8845.Triple.Nu3

#print axioms XiPrime8845.Triple.Nu3.nu3F_eq_inclExcl
