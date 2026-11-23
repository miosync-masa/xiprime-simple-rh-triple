/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.GammaPlane
import RHTriple.MixedGate

/-! The changes of variables in (3.40)–(3.42). The all-gamma integral
has prefactor `T*L`; an equal-index prime pair has prefactor `T/L`. -/

noncomputable section
open Complex MeasureTheory Filter Topology

namespace XiPrime8845.RHTriple

def focusedTest (Φ : ℝ × ℝ → ℂ) (w a : ℝ) (x : ℝ × ℝ) : ℂ :=
  Φ (a-x.1/w, -a-x.2/w)

theorem focusedTest_affine (Φ : ℝ × ℝ → ℂ) {w : ℝ} (hw : 0 < w) (a : ℝ) :
    focusedTest Φ w a = Φ ∘ (planeAffine (w*a, w*(-a)) (-w) (by linarith)).symm := by
  funext x
  unfold focusedTest
  apply congrArg Φ
  apply Prod.ext <;> dsimp [planeAffine] <;> field_simp <;> ring

theorem focusedTest_continuous {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ) (w a : ℝ) :
    Continuous (focusedTest Φ w a) := by unfold focusedTest; fun_prop

theorem focusedTest_compact {Φ : ℝ × ℝ → ℂ} (hΦc : HasCompactSupport Φ) {w : ℝ}
    (hw : 0 < w) (a : ℝ) : HasCompactSupport (focusedTest Φ w a) := by
  rw [focusedTest_affine Φ hw a]
  exact hΦc.comp_homeomorph _

theorem planeProduct_rescale_height {Φ : ℝ × ℝ → ℂ} {A B C : ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hA : Continuous A)
    (hB : Continuous B) (hC : Continuous C) {T L : ℝ} (hT : 0 < T) (hL : 0 < L) (a : ℝ) :
    (∫ x, Φ x * (A (T*(a-frequencyShift L 0 x)) * B (T*(-a-frequencyShift L 1 x)) *
      C (-(T*frequencyShift L 2 x)))) =
      ((T*L)⁻¹)^2 • planeProduct (focusedTest Φ (T*L) (a/L)) A B C := by
  let w := T*L
  have hw : 0 < w := mul_pos hT hL
  have he : w*(a/L) = T*a := by unfold w; field_simp
  have he' : w*(-(a/L)) = T*(-a) := by simpa only [mul_neg] using congrArg Neg.neg he
  rw [focusedTest_affine Φ hw]
  have H := planeProduct_rescale hΦ hΦc hA hB hC (w*(a/L),w*(-(a/L)))
    (show -w ≠ 0 by linarith)
  rw [show |(-w)⁻¹| = w⁻¹ by rw [inv_neg,abs_neg,abs_of_pos (inv_pos.mpr hw)]] at H
  rw [← H]
  apply integral_congr_ae
  filter_upwards [] with x
  change Φ x*(A (T*(a-L*x.1))*B (T*(-a-L*x.2))*C (-(T* -(L*x.1+L*x.2)))) =
    Φ x*(A ((-w)*x.1+w*(a/L))*B ((-w)*x.2+w*(-(a/L)))*
      C (-((-w)*x.1+w*(a/L)+((-w)*x.2+w*(-(a/L))))))
  rw [he, he']
  congr 3 <;> unfold w <;> ring

private theorem gammaFactor_normalized (k : ℝ → ℂ) {T : ℝ} (ht : 0 < T)
    (hL : 0 < Real.log T) (b : ℝ) :
    gammaFactor (dilate k T) b = ((T*Real.log T : ℝ) : ℂ)*normalizedGamma k T (-(T*b)) := by
  have hc : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [gammaFactor_dilate k ht, normalizedGamma, Complex.ofReal_mul, mul_assoc]
  field_simp

theorem allGamma_rescale {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {T : ℝ} (hT : 1 < T) (p : ℝ) :
    mixedEFIntegral k Φ p T 2 2 2 = ((T*Real.log T : ℝ) : ℂ) *
      planeProduct (focusedTest Φ (T*Real.log T) 0) (normalizedGamma k T)
        (normalizedGamma k T) (normalizedGamma k T) := by
  let L := Real.log T
  let W := T*L
  let G := normalizedGamma k T
  have ht : 0 < T := by linarith
  have hL : 0 < L := Real.log_pos hT
  have hW : (W:ℂ) ≠ 0 := by exact_mod_cast (mul_pos ht hL).ne'
  have hg := normalizedGamma_continuous hk hkc ht
  have H := planeProduct_rescale_height hΦ hΦc hg hg hg ht hL 0
  rw [zero_div] at H
  let F (x : ℝ × ℝ) := Φ x * (G (-(T*frequencyShift L 0 x)) * G (-(T*frequencyShift L 1 x)) *
    G (-(T*frequencyShift L 2 x)))
  have he : (∫ x, F x) = W⁻¹^2 • planeProduct (focusedTest Φ W 0) G G G := by
    unfold F
    simpa only [zero_sub, neg_zero, mul_neg] using H
  calc
    _ = (W:ℂ)^3 * ∫ x, F x := by
      unfold mixedEFIntegral
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      change Φ x * (gammaFactor (dilate k T) (frequencyShift L 0 x) *
        gammaFactor (dilate k T) (frequencyShift L 1 x) *
        gammaFactor (dilate k T) (frequencyShift L 2 x)) = _
      simp only [F, gammaFactor_normalized k ht hL]
      change Φ x * ((W:ℂ)*G _ * ((W:ℂ)*G _) * ((W:ℂ)*G _)) = _
      ring
    _ = _ := by
      rw [he, real_smul, Complex.ofReal_pow, Complex.ofReal_inv]
      field_simp
      rfl

theorem pairedKernel_rescale {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {T : ℝ} (hT : 1 < T) (a : ℝ) :
    twoPrimeGamma k Φ T (Real.log T) a (-a) = ((T/Real.log T : ℝ) : ℂ) *
      planeProduct (focusedTest Φ (T*Real.log T) (a/Real.log T)) k k (normalizedGamma k T) := by
  let L := Real.log T
  let W := T*L
  let G := normalizedGamma k T
  have ht : 0 < T := by linarith
  have hL : 0 < L := Real.log_pos hT
  have htc : (T:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hLc : (L:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  let F (x : ℝ × ℝ) := Φ x * (k (T*(a-frequencyShift L 0 x)) *
    k (T*(-a-frequencyShift L 1 x)) * G (-(T*frequencyShift L 2 x)))
  have H : (∫ x, F x) = W⁻¹^2 • planeProduct (focusedTest Φ W (a/L)) k k G :=
    planeProduct_rescale_height hΦ hΦc hk.continuous hk.continuous
      (normalizedGamma_continuous hk hkc ht) ht hL a
  calc
    _ = ((T:ℂ)^2*(W:ℂ)) * ∫ x, F x := by
      unfold twoPrimeGamma
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      change Φ x * (dilate k T (a-frequencyShift L 0 x) *
        dilate k T (-a-frequencyShift L 1 x) *
        gammaFactor (dilate k T) (frequencyShift L 2 x)) = _
      simp only [F, dilate, gammaFactor_normalized k ht hL]
      change Φ x * ((T:ℂ)*k _*((T:ℂ)*k _)*((W:ℂ)*G _)) = _
      ring
    _ = _ := by
      rw [H, real_smul]
      simp only [W, L, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_inv]
      field_simp
      rfl

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.allGamma_rescale
#print axioms XiPrime8845.RHTriple.pairedKernel_rescale
