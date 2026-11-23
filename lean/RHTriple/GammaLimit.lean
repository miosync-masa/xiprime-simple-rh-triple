/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.GammaBounds

/-! The normalized ζ gamma kernel converges uniformly to the input kernel.
It is not claimed to converge in L¹ on the entire real line. -/

noncomputable section
open Complex MeasureTheory Filter Topology

namespace XiPrime8845.RHTriple
open Zeta23

def normalizedGamma (k : ℝ → ℂ) (T x : ℝ) : ℂ :=
  scaledGamma k T x / (Real.log T : ℂ)

private abbrev leadingMu : ℝ := 1/(2*Real.pi)

theorem mu_scaled_tendsto {r : ℝ} (hr : r ≠ 0) :
    Tendsto (fun T : ℝ => mu (T*r)/Real.log T) atTop (𝓝 leadingMu) := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  let z := Real.log (|r|/(2*Real.pi))
  let D := |C| + leadingMu*|z|
  have hD : 0 ≤ D := by unfold D leadingMu; positivity
  have hA : 0 < |r| := abs_pos.mpr hr
  have hL := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h0 : Tendsto (fun T : ℝ => D / Real.log T) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, div_eq_mul_inv] using hL.const_mul D
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ h0
  filter_upwards [eventually_ge_atTop (|r|⁻¹), eventually_gt_atTop (1:ℝ)] with T hTr hT
  have ht : 0 < T := by linarith
  have hl := Real.log_pos hT
  have hh : 1 ≤ |T*r| := by
    rw [abs_mul, abs_of_pos ht]
    exact (inv_le_iff_one_le_mul₀ hA).mp hTr
  have hsq : 1 ≤ (T*r)^2 := by rw [← sq_abs]; nlinarith
  have hE := hC (T*r) hh
  have hlog : Real.log (|T*r|/(2*Real.pi)) = Real.log T+z := by
    rw [abs_mul, abs_of_pos ht, mul_div_assoc, Real.log_mul ht.ne'
      (div_pos hA (by positivity)).ne']
  rw [hlog] at hE
  have hErr : |mu (T*r) - leadingMu * (Real.log T+z)| ≤ |C| :=
    hE.trans ((div_le_iff₀ (by positivity : 0 < (T*r)^2)).2
      (by nlinarith only [le_abs_self C, mul_nonneg (abs_nonneg C) (sub_nonneg.mpr hsq)]))
  rw [Real.norm_eq_abs, show mu (T*r)/Real.log T-leadingMu =
    (mu (T*r)-leadingMu*Real.log T)/Real.log T by field_simp, abs_div, abs_of_pos hl]
  apply div_le_div_of_nonneg_right _ hl.le
  rw [show mu (T*r)-leadingMu*Real.log T =
    (mu (T*r)-leadingMu*(Real.log T+z))+leadingMu*z by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (show 0 ≤ leadingMu by unfold leadingMu; positivity)]
  exact add_le_add hErr le_rfl

private def gammaProfileError (k : ℝ → ℂ) (T r : ℝ) : ℝ :=
  ‖paperFT k r‖ * |mu (T*r)/Real.log T-leadingMu|

private theorem gammaProfileError_tendsto {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Tendsto (fun T : ℝ => ∫ r, gammaProfileError k T r) atTop (𝓝 0) := by
  obtain ⟨C,hC,hμ⟩ := mu_log_bound
  have hF := EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hk hkc)
  let B (r : ℝ) := (C+leadingMu)*‖paperFT k r‖ + C*(‖paperFT k r‖*Real.log (2+|r|))
  have hB : Integrable B := (hF.norm.const_mul _).add ((paperFT_log_integrable hk hkc).const_mul _)
  have hm (T : ℝ) : AEStronglyMeasurable (gammaProfileError k T) (volume : Measure ℝ) :=
    hF.norm.aestronglyMeasurable.mul
      (((gammaFacts.smooth.continuous.comp (continuous_const.mul continuous_id)).div_const _).sub
        continuous_const).abs.aestronglyMeasurable
  have hmajor : ∀ᶠ T : ℝ in atTop, ∀ᵐ r ∂(volume : Measure ℝ), ‖gammaProfileError k T r‖ ≤ B r := by
    filter_upwards [eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hL
    filter_upwards [] with r
    have ht : 0 < T := by linarith
    have hl : 0 < Real.log T := by linarith
    have hR : 0 < 2 + |r| := by positivity
    have hs : Real.log (2+|T*r|) ≤ Real.log T + Real.log (2+|r|) := by
      rw [← Real.log_mul ht.ne' hR.ne', abs_mul, abs_of_pos ht]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hlog0 := Real.log_nonneg (show 1 ≤ 2+|r| by linarith [abs_nonneg r])
    have hbound : |mu (T*r)/Real.log T| ≤ C + C * Real.log (2+|r|) := by
      rw [abs_div, abs_of_pos hl, div_le_iff₀ hl]
      have hm' := (hμ (T*r)).trans (mul_le_mul_of_nonneg_left hs hC.le)
      nlinarith only [hm', mul_nonneg (mul_nonneg hC.le hlog0) (sub_nonneg.mpr hL)]
    rw [gammaProfileError, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ ‖paperFT k r‖ * (|mu (T*r)/Real.log T| + |leadingMu|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (norm_nonneg _)
      _ ≤ ‖paperFT k r‖ * (C + C * Real.log (2+|r|) + leadingMu) := by
        rw [abs_of_nonneg (show 0 ≤ leadingMu by unfold leadingMu; positivity)]
        gcongr
      _ = B r := by unfold B; ring
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
    simpa using (ae_iff.mpr (by simp : (volume : Measure ℝ) {x : ℝ | ¬x ≠ 0} = 0))
  have hlim : ∀ᵐ r ∂(volume : Measure ℝ),
      Tendsto (fun T => gammaProfileError k T r) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hne] with r hr
    have h := ((mu_scaled_tendsto hr).sub_const leadingMu).abs.const_mul ‖paperFT k r‖
    simpa only [gammaProfileError, sub_self, abs_zero, mul_zero] using h
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence B
      (Eventually.of_forall hm) hmajor hB hlim

/-- A common bound on the error, tending to zero independently of the frequency. -/
theorem normalizedGamma_uniform {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ T in atTop, ∀ x, ‖normalizedGamma k T x-k x‖ ≤ e T := by
  refine ⟨fun T => ∫ r, gammaProfileError k T r, gammaProfileError_tendsto hk hkc, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  intro x
  have ht : 0 < T := by linarith
  have hl : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT).ne'
  have hF := EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hk hkc)
  let U (r : ℝ) := inverseProfile k x r
  have hU : Integrable U := hF.mul_bdd
    ((continuous_phase.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable)
    (c := 1) (Eventually.of_forall fun _ => (norm_phase _).le)
  let V (r : ℝ) := (paperFT k r * (mu (T*r) : ℂ))*phase (-(r*x))
  have hV : Integrable V := by
    have H := (gammaWeight_integrable (dilate_contDiff hk T) (dilate_hasCompactSupport hkc ht)).comp_mul_left' ht.ne'
    have H' : Integrable (fun r : ℝ => paperFT k r * (mu (T*r) : ℂ)) := by
      apply H.congr
      filter_upwards [] with r
      unfold gammaWeight
      rw [paperFT_dilate k ht, Complex.ofReal_mul, mul_comm (T:ℂ),
        mul_div_cancel_right₀ _ (by exact_mod_cast ht.ne')]
    exact H'.mul_bdd
      ((continuous_phase.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable)
      (c := 1) (Eventually.of_forall fun _ => (norm_phase _).le)
  have hP : (∫ r, U r)*(leadingMu:ℂ) = k x := by
    change (∫ r, inverseProfile k x r) * (leadingMu : ℂ) = _
    rw [integral_inverseProfile hk hkc]
    push_cast
    field_simp [Real.pi_ne_zero]
  change ‖(∫ r, V r)/(Real.log T : ℂ)-k x‖ ≤ _
  rw [← hP, ← integral_div, ← integral_mul_const, ← integral_sub (hV.div_const _) (hU.mul_const _)]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [] with r
  have he : V r / (Real.log T : ℂ)-U r*(leadingMu : ℂ) =
      ((paperFT k r)*((mu (T*r)/Real.log T-leadingMu : ℝ) : ℂ))*phase (-(r*x)) := by
    unfold V U inverseProfile
    push_cast
    field_simp
  rw [he, norm_mul, norm_phase, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, gammaProfileError]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.mu_scaled_tendsto
#print axioms XiPrime8845.RHTriple.normalizedGamma_uniform
