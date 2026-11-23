/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MainRescale

/-! Replace the shifted test by its value at the centre of the two
localized slots, uniformly in that centre. The height constant is left
in frequency-profile form, with both independent coordinates explicit. -/

noncomputable section
open Complex MeasureTheory Filter Topology

namespace XiPrime8845.RHTriple

def heightTripleMass (k : ℝ → ℂ) : ℂ := planeProduct (fun _ => 1) k k k

theorem focusedTest_uniform_bound {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ w a x, ‖focusedTest Φ w a x‖ ≤ M := by
  obtain ⟨B,hB⟩ := hΦc.isCompact.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max 0 B, le_max_left _ _, fun w a x => ?_⟩
  let y := (a-x.1/w, -a-x.2/w)
  change ‖Φ y‖ ≤ max 0 B
  by_cases hy : y ∈ tsupport Φ
  · exact (hB y hy).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
    exact le_max_left _ _

private theorem core_integrable {k : ℝ → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    Integrable (fun x : ℝ × ℝ => k x.1 * k x.2 * k (-(x.1+x.2))) := by
  have hi := hk.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc
  obtain ⟨M,hm⟩ := hkc.isCompact.exists_bound_of_continuousOn hk.continuousOn
  apply (hi.mul_prod hi).mul_bdd (c := max 0 M)
    (hk.comp (continuous_fst.add continuous_snd).neg).aestronglyMeasurable
  filter_upwards [] with x
  change ‖k (-(x.1+x.2))‖ ≤ max 0 M
  by_cases hx : -(x.1+x.2) ∈ tsupport k
  · exact (hm _ hx).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_left _ _

theorem focused_k_uniform {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∀ a : ℝ,
      ‖planeProduct (focusedTest Φ (T*Real.log T) a) k k k - Φ (a,-a)*heightTripleMass k‖ ≤ ε := by
  intro ε hε
  let H (x : ℝ × ℝ) := k x.1*k x.2*k (-(x.1+x.2))
  have hi : Integrable H := core_integrable hk hkc
  let J := ∫ x, ‖H x‖
  have hj : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨R,hR⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  obtain ⟨δ,hδ,hδb⟩ := Metric.uniformContinuous_iff.mp (hΦc.uniformContinuous_of_continuous hΦ)
    (ε/(1+J)) (div_pos hε (by positivity))
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_gt_atTop (R/δ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hT' hL
  have hw : 0 < T*Real.log T := by positivity
  have hd : R/(T*Real.log T) < δ := by
    apply (div_lt_iff₀ hw).2
    have hR' := (div_lt_iff₀ hδ).1 hT'
    have h' := mul_nonneg (show 0 ≤ δ*T by positivity) (sub_nonneg.mpr hL)
    nlinarith only [hR',h']
  intro a
  let P := focusedTest Φ (T*Real.log T) a
  have hP : Integrable (fun x => P x * H x) := planeProduct_integrable
    (focusedTest_continuous hΦ _ _) (focusedTest_compact hΦc hw a) hk hk hk
  have heq : planeProduct P k k k - Φ (a,-a)*heightTripleMass k =
      ∫ x, P x * H x - Φ (a,-a)*H x := by
    rw [integral_sub hP (hi.const_mul _), integral_const_mul]
    simp only [planeProduct, heightTripleMass, one_mul, H]
  rw [heq]
  have hb (x : ℝ × ℝ) : ‖P x * H x - Φ (a,-a) * H x‖ ≤ (ε/(1+J))*‖H x‖ := by
    by_cases hx : H x = 0
    · simp [hx]
    have h1 : |x.1| ≤ R := hR _ (fun hh => hx (by simp [H,hh]))
    have h2 : |x.2| ≤ R := hR _ (fun hh => hx (by simp [H,hh]))
    have hdist : dist (a-x.1/(T*Real.log T), -a-x.2/(T*Real.log T)) (a,-a) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      change max |a-x.1/(T*Real.log T)-a| |-a-x.2/(T*Real.log T)- -a| < δ
      rw [show a-x.1/(T*Real.log T)-a = -(x.1/(T*Real.log T)) by ring,
        show -a-x.2/(T*Real.log T)- -a = -(x.2/(T*Real.log T)) by ring,
        abs_neg, abs_neg, abs_div, abs_div, abs_of_pos hw]
      apply max_lt
      · exact (div_le_div_of_nonneg_right h1 hw.le).trans_lt hd
      · exact (div_le_div_of_nonneg_right h2 hw.le).trans_lt hd
    have h := hδb hdist
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (by
      simpa only [dist_eq_norm, P, focusedTest] using h.le) (norm_nonneg _)
  calc
    _ ≤ ∫ x, ‖P x * H x - Φ (a,-a)*H x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (ε/(1+J))*‖H x‖ := integral_mono (hP.sub (hi.const_mul _)).norm (hi.norm.const_mul _) hb
    _ = (ε/(1+J))*J := integral_const_mul _ _
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1+J)]
      linarith

theorem paired_plane_uniform {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    ∀ ε > 0, ∀ᶠ T in atTop, ∀ a : ℝ,
      ‖planeProduct (focusedTest Φ (T*Real.log T) a) k k (normalizedGamma k T) -
         Φ (a,-a)*heightTripleMass k‖ ≤ ε := by
  intro ε hε
  obtain ⟨M,hM,hM'⟩ := focusedTest_uniform_bound hΦ hΦc
  obtain ⟨e,he,hEb⟩ := normalizedGamma_uniform hk hkc
  let J := ∫ x, ‖k x‖
  have hi := hk.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc
  have h0 : Tendsto (fun T => M*J^2*e T) atTop (𝓝 0) := by simpa using he.const_mul (M*J^2)
  filter_upwards [hEb, eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    h0.eventually_le_const (show 0 < ε/2 by linarith), focused_k_uniform hk.continuous hkc hΦ hΦc
      (ε/2) (by linarith)] with T hE hT hL hεE hεK
  intro a
  let P := focusedTest Φ (T*Real.log T) a
  let G := normalizedGamma k T
  let Err := G-k
  have hP := focusedTest_continuous hΦ (T*Real.log T) a
  have hPc := focusedTest_compact hΦc (show 0 < T*Real.log T by positivity) a
  have hG : Continuous G := normalizedGamma_continuous hk hkc (by linarith)
  have hEq : planeProduct P k k G - planeProduct P k k k = planeProduct P k k Err := by
    unfold planeProduct
    rw [← integral_sub (planeProduct_integrable hP hPc hk.continuous hk.continuous hG)
      (planeProduct_integrable hP hPc hk.continuous hk.continuous hk.continuous)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Err, Pi.sub_apply]
    ring
  have B := planeProduct_bound hP hPc hk.continuous hk.continuous (hG.sub hk.continuous)
     hi hi hM ((norm_nonneg _).trans (hE 0)) (hM' _ _) hE
  change ‖planeProduct P k k Err‖ ≤ M*e T*(J*J) at B
  have hb : ‖planeProduct P k k Err‖ ≤ ε/2 := B.trans (by
    rw [show M*e T*(J*J) = M*J^2*e T by ring]
    exact hεE)
  rw [show planeProduct P k k G - Φ (a,-a)*heightTripleMass k =
    (planeProduct P k k G - planeProduct P k k k) +
      (planeProduct P k k k - Φ (a,-a)*heightTripleMass k) by abel, hEq]
  exact (norm_add_le _ _).trans (by linarith [hεK a])

theorem allGamma_normalized_tendsto {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (p : ℝ) :
    Tendsto (fun T => mixedEFIntegral k Φ p T 2 2 2 / ((T*Real.log T : ℝ):ℂ))
      atTop (𝓝 (Φ (0,0)*heightTripleMass k)) := by
  obtain ⟨M,hM,hB⟩ := focusedTest_uniform_bound hΦ hΦc
  let P (T : ℝ) := focusedTest Φ (T*Real.log T) 0
  have hP : ∀ᶠ T in atTop, Continuous (P T) ∧ HasCompactSupport (P T) ∧ ∀ x, ‖P T x‖ ≤ M := by
    filter_upwards [eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with T ht hL
    exact ⟨focusedTest_continuous hΦ _ _, focusedTest_compact hΦc (by positivity) _, hB _ _⟩
  have hG := normalizedGamma_plane_replace hk hkc hM hP
  have hK : Tendsto (fun T => planeProduct (P T) k k k) atTop (𝓝 (Φ (0,0)*heightTripleMass k)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [focused_k_uniform hk.continuous hkc hΦ hΦc (ε/2) (by linarith)] with T hT
    have H := hT 0
    simp only [neg_zero] at H
    rw [dist_eq_norm]
    exact H.trans_lt (by linarith)
  have H := hG.add hK
  rw [zero_add] at H
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  change (planeProduct (P T) (normalizedGamma k T) (normalizedGamma k T)
      (normalizedGamma k T) - planeProduct (P T) k k k) +
      planeProduct (P T) k k k = _
  rw [sub_add_cancel]
  have hTL : ((T*Real.log T : ℝ):ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (show T ≠ 0 by linarith) (Real.log_pos hT).ne'
  rw [allGamma_rescale hk hkc hΦ hΦc hT, mul_comm, mul_div_cancel_right₀ _ hTL]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.focused_k_uniform
#print axioms XiPrime8845.RHTriple.paired_plane_uniform
#print axioms XiPrime8845.RHTriple.allGamma_normalized_tendsto
