/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairHeight
import RHTriple.PolarFactor
import RHTriple.GammaLimit
import RHTriple.ZetaScale

/-! The all-equal index block of inclusion-exclusion has just one zero
sum, with height h³. At frequency zero the prime term vanishes. -/

noncomputable section
open MeasureTheory Filter Topology Complex
open scoped Convolution FourierTransform

namespace XiPrime8845.RHTriple
open Zeta23

def smoothedSingle (k : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∑' ρ : ZetaZero, (zetaZeroConfig.mult ρ : ℂ) * paperFT k ((ρ : ℂ).im / (T : ℂ))

theorem smoothedSingle_normalized_tendsto (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Tendsto (fun T : ℝ => smoothedSingle k T / ((T*Real.log T : ℝ):ℂ))
      atTop (𝓝 (k 0)) := by
  obtain ⟨R, hR0⟩ := EF.exists_abs_le_of_hasCompactSupport hkc
  let U := max R 0
  have hU : 0 ≤ U := le_max_right _ _
  have hR (x : ℝ) (hx : k x ≠ 0) : |x| ≤ U := (hR0 x hx).trans (le_max_left _ _)
  let B := Real.log 2 / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hfloor : ⌊Real.exp B⌋₊ < 2 := by
    apply (Nat.floor_lt (Real.exp_pos _).le).2
    change Real.exp B < (2:ℝ)
    have h := Real.log_pos (by norm_num : (1:ℝ) < 2)
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]
    exact Real.exp_lt_exp.mpr (by dsimp [B]; linarith)
  have hp' (T : ℝ) : primeFactor (dilate k T) B 0 = 0 := by
    unfold primeFactor
    rw [Finset.sum_eq_zero]
    · simp
    · intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      have he : n = 1 := by omega
      subst n
      simp
  have hs : ∀ᶠ T : ℝ in atTop, smoothedSingle k T =
      poleFactor (dilate k T) 0 + (T:ℂ) * scaledGamma k T 0 := by
    filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop (U/B)] with T hT hcut
    have ht : 0 < T := by linarith
    have hsd (x : ℝ) (hx : dilate k T x ≠ 0) : |x| ≤ B := by
      have hh := hR (T*x) (fun he => hx (by simp [dilate, he]))
      rw [abs_mul, abs_of_pos ht] at hh
      exact (le_of_mul_le_mul_left (hh.trans (by
        exact (div_le_iff₀ hB).mp hcut)) ht)
    have hsplit := literatureRHS_split (k := dilate k T) hsd
      (show B + |(0:ℝ)| ≤ B by simp)
    rw [hp', add_zero, gammaFactor_dilate k ht, mul_zero, neg_zero] at hsplit
    rw [shifted_EF hRH (dilate_contDiff hk T) (dilate_hasCompactSupport hkc ht)] at hsplit
    have hg (ρ : ZetaZero) : gammaOf (ρ : ℂ) = ((ρ : ℂ).im : ℂ) := by
      apply Complex.ext
      · simp [WeilEF.gammaOf_re]
      · simp [WeilEF.gammaOf_im, RH_implies_on_line hRH ρ.property]
    simpa only [pairPhaseSum, heightWeight, paperFT_dilate _ ht, hg,
      mul_zero, phase, ofReal_zero, exp_zero, mul_one, smoothedSingle] using hsplit
  have hG : Tendsto (fun T : ℝ => normalizedGamma k T 0) atTop (𝓝 (k 0)) := by
    obtain ⟨e, he, hE⟩ := normalizedGamma_uniform hk hkc
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hE.mono fun T h => h 0) he
  have hP : Tendsto (fun T : ℝ => poleFactor (dilate k T) 0 / ((T*Real.log T : ℝ):ℂ))
      atTop (𝓝 0) := by
    let C := 2*Real.exp (U/2)*(∫ x, ‖k x‖)
    have hbase : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
      (tendsto_const_nhds.div_atTop tendsto_id)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbase
    filter_upwards [eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with T hT hL
    have ht : 0 < T := by linarith
    have h := scaledPoleFactor_norm_le
      (hk.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc) hU hR hT.le 0
    simp only [abs_zero, zero_div, Real.exp_zero, mul_one] at h
    rw [norm_div, norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ T*Real.log T)]
    exact (div_le_div_of_nonneg_right h (by positivity)).trans
      (div_le_div_of_nonneg_left (h.trans' (norm_nonneg _)) ht (by nlinarith))
  refine ((hP.add hG).congr' ?_).trans ?_
  · filter_upwards [hs, eventually_gt_atTop (1:ℝ)] with T he hT
    rw [he, add_div, normalizedGamma, ofReal_mul]
    have hn : (T:ℂ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by linarith)
    rw [show (T:ℂ)*scaledGamma k T 0 / ((T:ℂ)*(Real.log T:ℂ)) =
      scaledGamma k T 0 / (Real.log T:ℂ) by rw [mul_div_mul_left _ _ hn]]
  · simp

def heightCubeProfile (k : ℝ → ℂ) : ℝ → ℂ :=
  heightSquareProfile k ⋆[ContinuousLinearMap.mul ℂ ℂ] k

theorem zeta_singleton_cube_normalized_tendsto (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Tendsto (fun T : ℝ => (∑' ρ : ZetaZero, (zetaZeroConfig.mult ρ : ℂ) *
      (paperFT k ((ρ : ℂ).im / (T : ℂ)))^3) / ((T*Real.log T : ℝ):ℂ)) atTop
      (𝓝 ((∫ r : ℝ, (paperFT k r)^3) / (2*Real.pi))) := by
  let k₃ := heightCubeProfile k
  have h₂ := heightSquareProfile_contDiff hk hkc
  have hc₂ := heightSquareProfile_compact hkc
  have hi := hk.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc
  have hi₂ := h₂.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hc₂
  have hc₃ : HasCompactSupport k₃ := hc₂.convolution (ContinuousLinearMap.mul ℂ ℂ) hkc
  have h₃ : ContDiff ℝ 2 k₃ := by
    let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
    change ContDiff ℝ 2 (heightSquareProfile k ⋆[B] k)
    exact hkc.contDiff_convolution_right B hi₂.locallyIntegrable hk
  have hft (r : ℝ) : paperFT k₃ r = (paperFT k r)^3 := by
    rw [EF.paperFT_ofReal_eq_fourier]
    change 𝓕 (heightSquareProfile k ⋆[ContinuousLinearMap.mul ℂ ℂ] k) _ = _
    rw [Real.fourier_mul_convolution_eq hi₂ hi, ← EF.paperFT_ofReal_eq_fourier,
      ← EF.paperFT_ofReal_eq_fourier, paperFT_heightSquareProfile hk hkc]
    ring
  have hmass : (∫ r : ℝ, (paperFT k r)^3) / (2*Real.pi) = k₃ 0 := by
    simp_rw [← hft]
    have H := integral_inverseProfile h₃ hc₃ 0
    simp only [inverseProfile, mul_zero, neg_zero, phase, ofReal_zero, exp_zero, mul_one] at H
    rw [H, mul_div_cancel_left₀ _ (by exact_mod_cast
      (show (2:ℝ)*Real.pi ≠ 0 by positivity))]
  rw [hmass]
  have H := smoothedSingle_normalized_tendsto hRH h₃ hc₃
  simpa only [smoothedSingle, ← Complex.ofReal_div, hft] using H

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.smoothedSingle_normalized_tendsto
#print axioms XiPrime8845.RHTriple.zeta_singleton_cube_normalized_tendsto
