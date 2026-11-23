/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedSlots

/-! The three two-slot restrictions of a three-point test. Phases in the
lemmas below use radians; multiplying the physical coordinates by 2π gives
the Fourier convention of GdLL (1). The diagonal fibre has Jacobian one. -/

noncomputable section
open MeasureTheory Filter

namespace XiPrime8845.RHTriple

def marginalX (Φ : ℝ × ℝ → ℂ) (t : ℝ) : ℂ := ∫ v : ℝ, Φ (t,v)
def marginalY (Φ : ℝ × ℝ → ℂ) (t : ℝ) : ℂ := ∫ v : ℝ, Φ (v,t)
def marginalD (Φ : ℝ × ℝ → ℂ) (t : ℝ) : ℂ := ∫ v : ℝ, Φ (v,t-v)

theorem marginals_eq_zero_of_hex {Φ : ℝ × ℝ → ℂ} {t η : ℝ}
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η)
    (ht : 1-η/2 < |t|) :
    marginalX Φ t = 0 ∧ marginalY Φ t = 0 ∧ marginalD Φ t = 0 := by
  have hx (v : ℝ) : Φ (t,v) = 0 := by
    by_contra h
    exact (not_le_of_gt ht) (by
      simpa [frequencyShift] using frequencyShift_hex_bound (L := 1)
        zero_le_one (hhex (t,v) h) 0)
  have hy (v : ℝ) : Φ (v,t) = 0 := by
    by_contra h
    exact (not_le_of_gt ht) (by
      simpa [frequencyShift] using frequencyShift_hex_bound (L := 1)
        zero_le_one (hhex (v,t) h) 1)
  have hd (v : ℝ) : Φ (v,t-v) = 0 := by
    by_contra h
    have H := frequencyShift_hex_bound (L := 1) zero_le_one (hhex (v,t-v) h) 2
    exact (not_le_of_gt ht) (by simpa [frequencyShift, add_sub_cancel] using H)
  simp [marginalX, marginalY, marginalD, hx, hy, hd]

theorem integral_marginalX {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (hcΦ : HasCompactSupport Φ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) :
    (∫ t : ℝ, marginalX Φ t * ψ t) = ∫ p : ℝ × ℝ, Φ p * ψ p.1 := by
  have hI : Integrable (fun p : ℝ × ℝ => Φ p * ψ p.1) :=
    (hΦ.mul (hψ.comp continuous_fst)).integrable_of_hasCompactSupport hcΦ.mul_right
  change _ = ∫ p : ℝ × ℝ, Φ p * ψ p.1 ∂(volume.prod volume)
  rw [integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [marginalX, integral_mul_const]

theorem integral_marginalY {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (hcΦ : HasCompactSupport Φ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) :
    (∫ t : ℝ, marginalY Φ t * ψ t) = ∫ p : ℝ × ℝ, Φ p * ψ p.2 := by
  change _ = ∫ p : ℝ × ℝ, Φ p * ψ p.2 ∂(volume.prod volume)
  rw [← integral_prod_swap (fun p : ℝ × ℝ => Φ p * ψ p.2)]
  exact integral_marginalX (hΦ.comp swap01.continuous) (hcΦ.comp_homeomorph swap01) hψ

theorem integral_marginalD {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (hcΦ : HasCompactSupport Φ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) :
    (∫ t : ℝ, marginalD Φ t * ψ t) = ∫ p : ℝ × ℝ, Φ p * ψ (p.1+p.2) := by
  have he (t : ℝ) : marginalD Φ t = marginalY (Φ ∘ swap12) (-t) := by
    unfold marginalD marginalY
    apply integral_congr_ae
    filter_upwards [] with v
    change Φ (v,t-v) = Φ (v,-(v+ -t))
    rw [show -(v + -t) = t-v by ring]
  have hrev := Measure.integral_comp_mul_left
    (fun t : ℝ => marginalD Φ t * ψ t) (-1)
  rw [inv_neg, inv_one, abs_neg, abs_one, one_smul] at hrev
  rw [← hrev]
  simp only [neg_mul, one_mul]
  simp_rw [he, neg_neg]
  have hneg : Continuous (fun x => ψ (-x)) := hψ.comp continuous_neg
  rw [integral_marginalY (hΦ.comp swap12.continuous) (hcΦ.comp_homeomorph swap12) hneg]
  have hG : Continuous (fun p : ℝ × ℝ => Φ p * ψ (p.1+p.2)) :=
    hΦ.mul (hψ.comp (continuous_fst.add continuous_snd))
  have hGc : HasCompactSupport (fun p : ℝ × ℝ => Φ p * ψ (p.1+p.2)) := hcΦ.mul_right
  convert integral_swap12 hG hGc using 2
  simp [swap12]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.marginals_eq_zero_of_hex
#print axioms XiPrime8845.RHTriple.integral_marginalX
#print axioms XiPrime8845.RHTriple.integral_marginalY
#print axioms XiPrime8845.RHTriple.integral_marginalD
