/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedSupport
import RHTriple.GammaBounds

/-! Uniform one-factor bounds for the actual zeta pole in the triple formula. -/

noncomputable section
open Complex MeasureTheory

namespace XiPrime8845.RHTriple
open Zeta23

theorem paperFT_imaginary_norm_le {k : ℝ → ℂ} {R : ℝ} (_hR : 0 ≤ R)
    (hk : Integrable k) (hs : ∀ x, k x ≠ 0 → |x| ≤ R)
    (y : ℂ) (hy : |y.im| ≤ (1:ℝ)/2) :
    ‖paperFT k y‖ ≤ Real.exp (R/2) * ∫ x, ‖k x‖ := by
  have h (x : ℝ) : ‖k x * Complex.exp (I * y * (x : ℂ))‖ ≤ Real.exp (R/2)*‖k x‖ := by
    rw [norm_mul, Complex.norm_exp]
    have he : (I * y * (x : ℂ)).re = -y.im*x := by simp [Complex.mul_re]
    rw [he, mul_comm (Real.exp _)]
    by_cases hx : k x = 0
    · simp [hx]
    · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |(-y.im)*x| := le_abs_self _
        _ = |y.im| * |x| := by rw [abs_mul, abs_neg]
        _ ≤ (1/2)*R := mul_le_mul hy (hs x hx) (abs_nonneg _) (by norm_num)
        _ = _ := by ring
  have hi : Integrable (fun x : ℝ => ‖k x * Complex.exp (I*y*(x:ℂ))‖) :=
    (hk.norm.const_mul (Real.exp (R/2))).mono'
      ((hk.aestronglyMeasurable.mul
        ((show Continuous (fun x : ℝ => Complex.exp (I*y*(x:ℂ))) by fun_prop).aestronglyMeasurable)).norm)
      (Filter.Eventually.of_forall fun x => by simpa only [norm_norm] using h x)
  unfold paperFT
  exact (norm_integral_le_integral_norm _).trans ((integral_mono hi
    (hk.norm.const_mul (Real.exp (R/2))) h).trans_eq (integral_const_mul _ _))

theorem scaledPoleFactor_norm_le {k : ℝ → ℂ} (hk : Integrable k)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ x, k x ≠ 0 → |x| ≤ R)
    {T : ℝ} (hT : 1 ≤ T) (b : ℝ) :
    ‖poleFactor (dilate k T) b‖ ≤ (2*Real.exp (R/2)*(∫ x, ‖k x‖))*Real.exp (|b|/2) := by
  have ht : 0 < T := by linarith
  have hnorm : |(I / 2 / (T : ℂ)).im| ≤ (1:ℝ)/2 := by
    have he : (I / 2 / (T : ℂ)).im = (1/2)/T := by simp [Complex.div_ofReal_im]
    rw [he, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ ht).2
    linarith
  have hneg : |(-I / 2 / (T : ℂ)).im| ≤ (1:ℝ)/2 := by
    simpa only [neg_div, neg_im, abs_neg] using hnorm
  have hb₁ : ‖Complex.exp (I * (I / 2) * (b : ℂ))‖ ≤ Real.exp (|b|/2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have he : (I*(I/2)*(b:ℂ)).re = -b/2 := by simp [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im]; ring
    linarith [neg_abs_le b]
  have hb₂ : ‖Complex.exp (I * (-I / 2) * (b : ℂ))‖ ≤ Real.exp (|b|/2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have he : (I*(-I/2)*(b:ℂ)).re = b/2 := by simp [Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im]; ring
    linarith [le_abs_self b]
  unfold poleFactor
  simp only [paperFT_dilate k ht]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (Real.exp (R/2)*(∫ x, ‖k x‖))*Real.exp (|b|/2) +
        (Real.exp (R/2)*(∫ x, ‖k x‖))*Real.exp (|b|/2) :=
      add_le_add
        (mul_le_mul (paperFT_imaginary_norm_le hR hk hs _ hnorm) hb₁ (norm_nonneg _) (by positivity))
        (mul_le_mul (paperFT_imaginary_norm_le hR hk hs _ hneg) hb₂ (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- The pole spends the budget of the full hexagon, not that of one
coordinate. The other two coordinates carry an exponential discount. -/
theorem hex_pole_budget {T η : ℝ} (hT : 1 ≤ T) {x : ℝ × ℝ}
    (hhex : |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    Real.exp (|frequencyShift (Real.log T) 2 x|/2) ≤ T^(1-η/2) *
      (Real.exp (-|frequencyShift (Real.log T) 0 x|/2) *
       Real.exp (-|frequencyShift (Real.log T) 1 x|/2)) := by
  have ht : 0 < T := by linarith
  let L := Real.log T
  have hL : 0 ≤ L := Real.log_nonneg hT
  have hb : |frequencyShift L 0 x| + |frequencyShift L 1 x| +
      |frequencyShift L 2 x| ≤ (2-η)*L := by
    change |L*x.1| + |L*x.2| + |-(L*x.1+L*x.2)| ≤ _
    rw [abs_neg, ← mul_add, abs_mul, abs_mul, abs_mul, abs_of_nonneg hL]
    nlinarith only [mul_le_mul_of_nonneg_left hhex hL]
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change |frequencyShift L 2 x|/2 ≤
    L*(1-η/2) + (-|frequencyShift L 0 x|/2 + -|frequencyShift L 1 x|/2)
  nlinarith only [hb, show L*(1-η/2)=(2-η)*L/2 by ring]

theorem gammaFactor_dilate_L1 {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ}, 1 ≤ T →
      Integrable (fun b => ‖gammaFactor (dilate k T) b‖) ∧
      (∫ b, ‖gammaFactor (dilate k T) b‖) ≤ C*(1+Real.log T) := by
  obtain ⟨C, hC, H⟩ := scaledGamma_L1 hk hkc
  refine ⟨C, hC, fun {T} hT => ?_⟩
  have ht : 0 < T := by linarith
  have he (b : ℝ) : ‖gammaFactor (dilate k T) b‖ = T*‖scaledGamma k T ((-T)*b)‖ := by
    rw [gammaFactor_dilate k ht, norm_mul, norm_real, Real.norm_of_nonneg ht.le, neg_mul]
  simp_rw [he]
  refine ⟨((H T hT).1.norm.comp_mul_left' (neg_ne_zero.mpr ht.ne')).const_mul T, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖scaledGamma k T x‖),
    smul_eq_mul, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr ht), ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  exact (H T hT).2

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.paperFT_imaginary_norm_le
#print axioms XiPrime8845.RHTriple.scaledPoleFactor_norm_le
#print axioms XiPrime8845.RHTriple.hex_pole_budget
#print axioms XiPrime8845.RHTriple.gammaFactor_dilate_L1
