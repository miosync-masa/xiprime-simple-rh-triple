/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PolarFactor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The pole estimate factors into two one-dimensional, damped L¹ costs.
No reciprocal log gap or decay of the height profile at ordinate zero is used. -/

noncomputable section
open Complex MeasureTheory Filter
open scoped Asymptotics

namespace XiPrime8845.RHTriple

theorem pole_last_plane_bound {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} {A B : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hA : Continuous A) (hB : Continuous B)
    {R M η T : ℝ} (hR : 0 ≤ R) (hs : ∀ x, k x ≠ 0 → |x| ≤ R)
    (hM : 0 ≤ M) (hMb : ∀ x, ‖Φ x‖ ≤ M) (hT : 1 ≤ T)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η)
    {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ u, 0 ≤ f u) (hg0 : ∀ u, 0 ≤ g u)
    (hbf : ∀ x : ℝ × ℝ, Φ x ≠ 0 →
      Real.exp (-|frequencyShift (Real.log T) 0 x|/2) *
        ‖A (frequencyShift (Real.log T) 0 x)‖ ≤ f x.1)
    (hbg : ∀ x : ℝ × ℝ, Φ x ≠ 0 →
      Real.exp (-|frequencyShift (Real.log T) 1 x|/2) *
        ‖B (frequencyShift (Real.log T) 1 x)‖ ≤ g x.2) :
    ‖∫ x, Φ x * (A (frequencyShift (Real.log T) 0 x) * B (frequencyShift (Real.log T) 1 x) *
      poleFactor (dilate k T) (frequencyShift (Real.log T) 2 x))‖ ≤
      M*(2*Real.exp (R/2)*(∫ b, ‖k b‖))*T^(1-η/2) * ((∫ b, f b)*(∫ b, g b)) := by
  let L := Real.log T
  let D := 2*Real.exp (R/2)*(∫ b, ‖k b‖)
  let C := M*D*T^(1-η/2)
  have ht : 0 < T := by linarith
  let F (x : ℝ × ℝ) := Φ x * (A (frequencyShift L 0 x) * B (frequencyShift L 1 x) *
    poleFactor (dilate k T) (frequencyShift L 2 x))
  have hAi : Continuous (fun x => A (frequencyShift L 0 x)) := hA.comp (frequencyShift_continuous L 0)
  have hBi : Continuous (fun x => B (frequencyShift L 1 x)) := hB.comp (frequencyShift_continuous L 1)
  have hPi : Continuous (fun x => poleFactor (dilate k T) (frequencyShift L 2 x)) :=
    (factors_continuous (dilate_contDiff hk T) (dilate_hasCompactSupport hkc ht) 0 0).comp
      (frequencyShift_continuous L 2)
  have hFi : Integrable F := (hΦ.mul ((hAi.mul hBi).mul hPi)).integrable_of_hasCompactSupport
    (show HasCompactSupport F from hΦc.mul_right)
  have hC : 0 ≤ C := by unfold C D; positivity
  have hmajor (x : ℝ × ℝ) : ‖F x‖ ≤ C*(f x.1*g x.2) := by
    by_cases hx : Φ x = 0
    · simpa [F, hx] using mul_nonneg hC (mul_nonneg (hf0 x.1) (hg0 x.2))
    let a := frequencyShift L 0 x
    let b := frequencyShift L 1 x
    let c := frequencyShift L 2 x
    have hpol : ‖poleFactor (dilate k T) c‖ ≤ D * Real.exp (|c|/2) :=
      scaledPoleFactor_norm_le (hk.continuous.integrable_of_hasCompactSupport hkc) hR hs hT c
    have hbudget : Real.exp (|c|/2) ≤ T^(1-η/2)*(Real.exp (-|a|/2)*Real.exp (-|b|/2)) :=
      hex_pole_budget hT (hhex x hx)
    calc
      _ = ‖Φ x‖*(‖A a‖*‖B b‖*‖poleFactor (dilate k T) c‖) := by simp [F, a, b, c]
      _ ≤ M*(‖A a‖*‖B b‖*(D*Real.exp (|c|/2))) := by gcongr; exact hMb x
      _ ≤ M*(‖A a‖*‖B b‖*(D*(T^(1-η/2)*(Real.exp (-|a|/2)*Real.exp (-|b|/2))))) := by
        gcongr
      _ = C*((Real.exp (-|a|/2)*‖A a‖)*(Real.exp (-|b|/2)*‖B b‖)) := by unfold C; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul (hbf x hx) (hbg x hx) (by positivity) (hf0 x.1)) hC
  have hd := (hf.mul_prod hg).const_mul C
  change ‖∫ x, F x‖ ≤ C*((∫ b, f b)*(∫ b, g b))
  calc
    _ ≤ ∫ x, ‖F x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ × ℝ, C*(f x.1*g x.2) := integral_mono hFi.norm hd hmajor
    _ = _ := by
      rw [integral_const_mul]
      change C*(∫ x : ℝ × ℝ, f x.1*g x.2 ∂((volume : Measure ℝ).prod volume)) = _
      rw [integral_prod_mul f g]

theorem littleO_height_power_polylog {F : ℝ → ℂ} {η C : ℝ} (hη : 0 < η)
    (hC : 0 ≤ C) (hF : ∀ᶠ T in atTop, ‖F T‖ ≤ C*T^(1-η/2)*(1+Real.log T)^4) :
    F =o[atTop] (fun T => T*Real.log T) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hsmall := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (show 0 < η/4 by positivity))
  have hs := (Asymptotics.isLittleO_iff.mp hsmall) (show (0:ℝ) < 1 by norm_num)
  have hlarge := (tendsto_rpow_atTop (show 0 < η/4 by positivity)).eventually_ge_atTop (16*C/ε)
  filter_upwards [hF, hs, hlarge, eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hS hbig hT1 hL
  have ht : 0 < T := by linarith
  have hL0 : 0 ≤ Real.log T := by linarith
  have hlog : (Real.log T)^4 ≤ T^(η/4) := by
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hL0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), show (4:ℝ)=(4:ℕ) by norm_num,
      Real.rpow_natCast] at hS
    exact hS
  have hb : 16*C ≤ T^(η/4)*ε := (div_le_iff₀ hε).mp hbig
  have hpow : T^(1-η/2) * T^(η/4) * T^(η/4) = T := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, show 1-η/2+η/4+η/4=1 by ring, Real.rpow_one]
  rw [Real.norm_of_nonneg (mul_nonneg ht.le hL0)]
  calc
    _ ≤ C*T^(1-η/2)*(1+Real.log T)^4 := hT
    _ ≤ C*T^(1-η/2)*(2*Real.log T)^4 := by gcongr; linarith
    _ = (16*C)*T^(1-η/2)*(Real.log T)^4 := by ring
    _ ≤ (16*C)*T^(1-η/2)*T^(η/4) := by gcongr
    _ ≤ (T^(η/4)*ε)*T^(1-η/2)*T^(η/4) := by gcongr
    _ = ε*T := by linear_combination ε * hpow
    _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hε.le ht.le) (sub_nonneg.mpr hL)]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pole_last_plane_bound
#print axioms XiPrime8845.RHTriple.littleO_height_power_polylog
