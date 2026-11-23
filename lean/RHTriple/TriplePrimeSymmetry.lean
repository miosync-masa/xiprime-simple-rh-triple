/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.TriplePrimeAssembly

/-! Permuting slots permutes the signed factors and pulls back the test.
Reversing every sign reflects BOTH the plane test and the height-frequency
profile. No parity of either function is required. -/

noncomputable section
open Complex MeasureTheory Filter Finset

namespace XiPrime8845.RHTriple

def reflect01 : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := (-x.1, -x.2)
  invFun x := (-x.1, -x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reflectHeight : ℝ ≃ₜ ℝ where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem integral_reflect01 {F : ℝ × ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    (∫ x, F (reflect01 x)) = ∫ x, F x := by
  have h₁ : Integrable F := hF.integrable_of_hasCompactSupport hFc
  have h₂ : Integrable (F ∘ reflect01) :=
    (hF.comp reflect01.continuous).integrable_of_hasCompactSupport (hFc.comp_homeomorph reflect01)
  change (∫ x, (F ∘ reflect01) x ∂(volume.prod volume)) = ∫ x, F x ∂(volume.prod volume)
  rw [integral_prod _ h₂, integral_prod _ h₁]
  have h (u : ℝ) : (∫ v, (F ∘ reflect01) (u,v)) = ∫ v, F (-u,v) := by
    change (∫ v : ℝ, F (-u,-v)) = ∫ v : ℝ, F (-u,v)
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using
      (Measure.integral_comp_mul_left (fun v : ℝ => F (-u,v)) (-1))
  simp_rw [h]
  simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using
    (Measure.integral_comp_mul_left (fun u : ℝ => ∫ v, F (u,v)) (-1))

theorem slots_reflect01 (L : ℝ) (x : ℝ × ℝ) (i : Fin 3) :
    frequencyShift L i (reflect01 x) = -frequencyShift L i x := by
  fin_cases i
  · change L*(-x.1) = -(L*x.1); ring
  · change L*(-x.2) = -(L*x.2); ring
  · change -(L*(-x.1)+L*(-x.2)) = -(-(L*x.1+L*x.2)); ring

theorem signedTriple_swap01 (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ)
    (N : ℕ) (T : ℝ) (s t u : Bool) :
    signedTripleIntegral k Φ N T s t u =
      signedTripleIntegral k (Φ ∘ swap01) N T t s u := by
  unfold signedTripleIntegral
  rw [← integral_swap01]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Function.comp_apply, (slots_swap01 (Real.log T) x).1,
    (slots_swap01 (Real.log T) x).2.1, (slots_swap01 (Real.log T) x).2.2]
  ring

theorem signedTriple_swap12 {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (N : ℕ) (T : ℝ) (s t u : Bool) :
    signedTripleIntegral k Φ N T s t u =
      signedTripleIntegral k (Φ ∘ swap12) N T s u t := by
  let F (x : ℝ × ℝ) := Φ x * (signedPrimeFactor k T N s (frequencyShift (Real.log T) 0 x) *
    signedPrimeFactor k T N t (frequencyShift (Real.log T) 1 x) *
    signedPrimeFactor k T N u (frequencyShift (Real.log T) 2 x))
  calc
    _ = ∫ x, F (swap12 x) :=
      (integral_swap12 (signedTripleIntegrand_continuous hk hΦ N T s t u)
        (hΦc.mul_right : HasCompactSupport F)).symm
    _ = _ := by
      unfold signedTripleIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [F, Function.comp_apply, (slots_swap12 (Real.log T) x).1,
        (slots_swap12 (Real.log T) x).2.1, (slots_swap12 (Real.log T) x).2.2]
      ring

private theorem signedPrimeFactor_reflect (k : ℝ → ℂ) (T : ℝ) (N : ℕ) (s : Bool) (b : ℝ) :
    signedPrimeFactor k T N s (-b) = signedPrimeFactor (k ∘ reflectHeight) T N (!s) b := by
  unfold signedPrimeFactor
  apply sum_congr rfl
  intro n _
  have h : signedLog (!s) n = -signedLog s n := by cases s <;> simp [signedLog]
  rw [h]
  simp only [dilate, Function.comp_apply]
  congr 3
  change T*(signedLog s n- -b) = -(T*(-signedLog s n-b))
  ring

theorem signedTriple_flip {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (N : ℕ) (T : ℝ) (s t u : Bool) :
    signedTripleIntegral k Φ N T s t u =
      signedTripleIntegral (k ∘ reflectHeight) (Φ ∘ reflect01) N T (!s) (!t) (!u) := by
  let F (x : ℝ × ℝ) := Φ x * (signedPrimeFactor k T N s (frequencyShift (Real.log T) 0 x) *
    signedPrimeFactor k T N t (frequencyShift (Real.log T) 1 x) *
    signedPrimeFactor k T N u (frequencyShift (Real.log T) 2 x))
  calc
    _ = ∫ x, F (reflect01 x) :=
      (integral_reflect01 (signedTripleIntegrand_continuous hk hΦ N T s t u)
        (hΦc.mul_right : HasCompactSupport F)).symm
    _ = _ := by
      unfold signedTripleIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [F, Function.comp_apply, slots_reflect01, signedPrimeFactor_reflect]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.signedTriple_swap01
#print axioms XiPrime8845.RHTriple.signedTriple_swap12
#print axioms XiPrime8845.RHTriple.signedTriple_flip
