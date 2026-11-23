/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairEFExpansion
import RHTriple.PairPrimeRescale
import RHTriple.PairGammaPrimeGap

/-! Uniform L¹ bounds on the two-point line and the actual prime/gamma
gap control the seven discarded terms at the common subcritical cutoff. -/

noncomputable section
open Complex MeasureTheory Filter Topology
open scoped Asymptotics

namespace XiPrime8845.RHTriple

private def link (Q A B : ℝ → ℂ) : ℂ := ∫ t : ℝ, Q t*(A t*B t)

private theorem link_le {Q A B : ℝ → ℂ}
    (hQ : Continuous Q) (hcQ : HasCompactSupport Q)
    (hA : Continuous A) (hB : Continuous B) (iB : Integrable (fun t => ‖B t‖))
    {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hq : ∀ t, ‖Q t‖ ≤ M)
    (ha : ∀ t, Q t ≠ 0 → B t ≠ 0 → ‖A t‖ ≤ C) :
    ‖link Q A B‖ ≤ M*C*(∫ t, ‖B t‖) := by
  have hi := (hQ.mul (hA.mul hB)).integrable_of_hasCompactSupport (μ := (volume : Measure ℝ))
    (hcQ.mul_right : HasCompactSupport (fun t => Q t*(A t*B t)))
  unfold link
  refine (norm_integral_le_integral_norm _).trans
    ((integral_mono hi.norm (iB.const_mul (M*C)) fun t => ?_).trans_eq (integral_const_mul _ _))
  by_cases h₁ : Q t = 0
  · simp [h₁, mul_nonneg (mul_nonneg hM hC) (norm_nonneg _)]
  by_cases h₂ : B t = 0
  · simp [h₂]
  change ‖Q t*(A t*B t)‖ ≤ M*C*‖B t‖
  simp only [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hq t) (ha t h₁ h₂) (norm_nonneg _) hM) (norm_nonneg _)

private theorem link_poles_le {Q A B : ℝ → ℂ}
    (hQ : Continuous Q) (hcQ : HasCompactSupport Q)
    (hA : Continuous A) (hB : Continuous B) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ t, Q t ≠ 0 → ‖A t‖ ≤ C) (hb : ∀ t, Q t ≠ 0 → ‖B t‖ ≤ D) :
    ‖link Q A B‖ ≤ C*D*(∫ t, ‖Q t‖) := by
  have hi := (hQ.mul (hA.mul hB)).integrable_of_hasCompactSupport (μ := (volume : Measure ℝ))
    (hcQ.mul_right : HasCompactSupport (fun t => Q t*(A t*B t)))
  have hiQ := (hQ.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hcQ).norm
  unfold link
  refine (norm_integral_le_integral_norm _).trans
    ((integral_mono hi.norm (hiQ.const_mul (C*D)) fun t => ?_).trans_eq (integral_const_mul _ _))
  by_cases h₁ : Q t = 0
  · simp [h₁]
  change ‖Q t*(A t*B t)‖ ≤ C*D*‖Q t‖
  simp only [norm_mul]
  rw [mul_comm ‖Q t‖]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (ha t h₁) (hb t h₁) (norm_nonneg _) hC) (norm_nonneg _)

private theorem link_comm (Q A B : ℝ → ℂ) : link Q A B = link Q B A := by
  unfold link
  simp_rw [mul_comm (A _) (B _)]

private theorem gamma_line_L1 {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ≥ 1, 1 ≤ Real.log T →
      Integrable (fun t => ‖gammaFactor (dilate k T) (Real.log T*t)‖) ∧
      (∫ t, ‖gammaFactor (dilate k T) (Real.log T*t)‖) ≤ C := by
  obtain ⟨A,hA,H⟩ := gammaFactor_dilate_L1 hk hkc
  refine ⟨2*A,by positivity,fun T hT hL => ?_⟩
  obtain ⟨hi,hh⟩ := H hT
  have hL0 : 0 < Real.log T := by linarith
  refine ⟨hi.comp_mul_left' hL0.ne',?_⟩
  rw [Measure.integral_comp_mul_left (fun t => ‖gammaFactor (dilate k T) t‖),
    abs_of_pos (inv_pos.mpr hL0), smul_eq_mul]
  apply (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hL0).le).trans
  rw [← div_eq_inv_mul, div_le_iff₀ hL0]
  nlinarith only [mul_nonneg hA (sub_nonneg.mpr hL)]

private theorem flipL1 {F : ℝ → ℝ} (hF : Integrable F) :
    Integrable (fun x => F (-x)) ∧ (∫ x, F (-x)) = ∫ x, F x := by
  exact ⟨by simpa only [neg_one_mul] using hF.comp_mul_left' (by norm_num : (-1:ℝ) ≠ 0),
    integral_neg_eq_self _ volume⟩

private theorem poleExp {d T t : ℝ} (hT : 1 < T) (ht : |t| ≤ d) :
    Real.exp (|Real.log T*t|/2) ≤ T^(d/2) := by
  rw [abs_mul, abs_of_pos (Real.log_pos hT), Real.rpow_def_of_pos (zero_lt_one.trans hT), Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left ht (Real.log_pos hT).le
  linarith only [h]

theorem smoothedPair_sub_survivors_isLittleO (hRH : RiemannHypothesis)
    {a b Q : ℝ → ℂ} (ha : ContDiff ℝ 2 a) (hca : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hcb : HasCompactSupport b)
    (hQ : Continuous Q) (hcQ : HasCompactSupport Q)
    {c d : ℝ} (hcd : c < d) (hd : 0 < d) (hd1 : d < 1)
    (hs : ∀ t, Q t ≠ 0 → |t| ≤ c) :
    (fun T => smoothedPair a b Q T - (pairGammaTerm a b Q T + pairPrimeTerm a b Q d T))
      =o[atTop] (fun T => T*Real.log T) := by
  obtain ⟨R₁,hR₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hca
  obtain ⟨R₂,hR₂⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hcb
  let R := max (max R₁ R₂) 0
  have hR : 0 ≤ R := le_max_right _ _
  have haR (x : ℝ) (hx : a x ≠ 0) : |x| ≤ R :=
    (hR₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hbR (x : ℝ) (hx : b x ≠ 0) : |x| ≤ R :=
    (hR₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  have ia : Integrable a := ha.continuous.integrable_of_hasCompactSupport hca
  have ib : Integrable b := hb.continuous.integrable_of_hasCompactSupport hcb
  obtain ⟨C₁,hC₁,hG₁⟩ := gamma_line_L1 ha hca
  obtain ⟨C₂,hC₂,hG₂⟩ := gamma_line_L1 hb hcb
  obtain ⟨M₀,hM₀⟩ := hcQ.isCompact.exists_bound_of_continuousOn hQ.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hqb (t : ℝ) : ‖Q t‖ ≤ M := by
    by_cases h : t ∈ tsupport Q
    · exact (hM₀ t h).trans (le_max_left _ _)
    · simp [image_eq_zero_of_notMem_tsupport h,hM]
  let A := ∫ x, ‖a x‖
  let B := ∫ x, ‖b x‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  let U := 2*Real.exp (R/2)*A
  let V := 2*Real.exp (R/2)*B
  have hU : 0 ≤ U := by unfold U; positivity
  have hV : 0 ≤ V := by unfold V; positivity
  let D := U*V*(∫ t, ‖Q t‖)+M*U*(4*d*B)+M*V*(4*d*A)+
    M*U*C₂+M*V*C₁+M*(40*A)*(4*d*B)+M*(40*B)*(4*d*A)
  have hD : 0 ≤ D := by
    unfold D
    have : 0 ≤ ∫ t, ‖Q t‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖smoothedPair a b Q T - (pairGammaTerm a b Q T + pairPrimeTerm a b Q d T)‖ ≤ D*T^d := by
    filter_upwards [smoothedPair_eventually_eq_factors hRH ha hca hb hcb
      (hQ.integrable_of_hasCompactSupport hcQ) hcd hs, eventually_gt_atTop (max 1 (8*R)),
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hEF hT' hL
    have hT : 1 < T := (le_max_left _ _).trans_lt hT'
    have ht : 0 < T := zero_lt_one.trans hT
    have hcut : R < T/8 := by linarith [(le_max_right 1 (8*R)).trans_lt hT']
    let L := Real.log T
    let r := T^(d/2)
    have hr : 1 ≤ r := Real.one_le_rpow hT.le (by positivity)
    have hrsq : r*r = T^d := by
      unfold r
      rw [← Real.rpow_add ht,show d/2+d/2=d by ring]
    let P₁ (t : ℝ) := primeFactor (dilate a T) (d*L) (L*t)
    let P₂ (t : ℝ) := primeFactor (dilate b T) (d*L) (-(L*t))
    let G₁ (t : ℝ) := gammaFactor (dilate a T) (L*t)
    let G₂ (t : ℝ) := gammaFactor (dilate b T) (-(L*t))
    let O₁ (t : ℝ) := poleFactor (dilate a T) (L*t)
    let O₂ (t : ℝ) := poleFactor (dilate b T) (-(L*t))
    have cP₁ : Continuous P₁ := (primeFactor_continuous (by unfold dilate; fun_prop) _).comp
      (continuous_const.mul continuous_id)
    have cP₂ : Continuous P₂ := (primeFactor_continuous (by unfold dilate; fun_prop) _).comp
      ((continuous_const.mul continuous_id).neg)
    have cG₁ : Continuous G₁ := (gammaFactor_continuous (gammaWeight_integrable
      (dilate_contDiff ha T) (dilate_hasCompactSupport hca ht))).comp (continuous_const.mul continuous_id)
    have cG₂ : Continuous G₂ := (gammaFactor_continuous (gammaWeight_integrable
      (dilate_contDiff hb T) (dilate_hasCompactSupport hcb ht))).comp ((continuous_const.mul continuous_id).neg)
    have cO₁ : Continuous O₁ := by unfold O₁ poleFactor; fun_prop
    have cO₂ : Continuous O₂ := by unfold O₂ poleFactor; fun_prop
    obtain ⟨iP₁,bP₁⟩ := primeFactor_line_norm_integrable_bound ha.continuous hca hd hT
    obtain ⟨iP₂',bP₂'⟩ := primeFactor_line_norm_integrable_bound hb.continuous hcb hd hT
    obtain ⟨iG₁,bG₁⟩ := hG₁ T hT.le hL
    obtain ⟨iG₂',bG₂'⟩ := hG₂ T hT.le hL
    obtain ⟨iP₂,eP₂⟩ : Integrable (fun t => ‖P₂ t‖) ∧
        (∫ t, ‖P₂ t‖) = ∫ t, ‖primeFactor (dilate b T) (d*L) (L*t)‖ := by
      simpa only [P₂,mul_neg] using flipL1 iP₂'
    obtain ⟨iG₂,eG₂⟩ : Integrable (fun t => ‖G₂ t‖) ∧
        (∫ t, ‖G₂ t‖) = ∫ t, ‖gammaFactor (dilate b T) (L*t)‖ := by
      simpa only [G₂,mul_neg] using flipL1 iG₂'
    have bP₂ : (∫ t, ‖P₂ t‖) ≤ (4*d*B)*r := eP₂.trans_le bP₂'
    have bG₂ : (∫ t, ‖G₂ t‖) ≤ C₂ := eG₂.trans_le bG₂'
    have Oa (t : ℝ) (hq : Q t ≠ 0) : ‖O₁ t‖ ≤ U*r :=
      (scaledPoleFactor_norm_le ia hR haR hT.le _).trans
        (mul_le_mul_of_nonneg_left (poleExp hT ((hs t hq).trans hcd.le)) hU)
    have Ob (t : ℝ) (hq : Q t ≠ 0) : ‖O₂ t‖ ≤ V*r := by
      have H := scaledPoleFactor_norm_le ib hR hbR hT.le (-(L*t))
      rw [abs_neg] at H
      exact H.trans (mul_le_mul_of_nonneg_left (poleExp hT ((hs t hq).trans hcd.le)) hV)
    have Ga (t : ℝ) (hp : P₂ t ≠ 0) : ‖G₁ t‖ ≤ 40*A := by
      apply pairGammaFactor_bounded_away ha hca haR ht hcut
      by_contra! h
      exact hp (pairPrimeFactor_zero_near_origin hbR ht (by linarith) (by
        rw [abs_neg]; exact h.le))
    have Gb (t : ℝ) (hp : P₁ t ≠ 0) : ‖G₂ t‖ ≤ 40*B := by
      apply pairGammaFactor_bounded_away hb hcb hbR ht hcut
      rw [abs_neg]
      by_contra! h
      exact hp (pairPrimeFactor_zero_near_origin haR ht (by linarith) h.le)
    let l (X Y : ℝ → ℂ) := link Q X Y
    have hI {X Y : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) :
        Integrable (fun t => Q t*(X t*Y t)) :=
      (hQ.mul (hX.mul hY)).integrable_of_hasCompactSupport hcQ.mul_right
    have hdecomp : smoothedPair a b Q T - (pairGammaTerm a b Q T+pairPrimeTerm a b Q d T) =
        l O₁ O₂ + l O₁ P₂ + l O₂ P₁ + l O₁ G₂ + l O₂ G₁ + l G₁ P₂ + l G₂ P₁ := by
      have z₁ {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
          l (X+Y) Z = l X Z+l Y Z := by
        unfold l link
        rw [← integral_add (hI hX hZ) (hI hY hZ)]
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [Pi.add_apply]
        ring
      have z₂ {X Y Z : ℝ → ℂ} (hX : Continuous X) (hY : Continuous Y) (hZ : Continuous Z) :
          l X (Y+Z) = l X Y+l X Z := by
        simp_rw [l,link_comm Q X]
        exact z₁ hY hZ hX
      rw [hEF]
      simp only [pairEFfactor,mul_neg]
      change l (O₁+P₁+G₁) (O₂+P₂+G₂) - (l G₁ G₂+l P₁ P₂) = _
      have hbreak {X : ℝ → ℂ} (hX : Continuous X) :
          l X (O₂+P₂+G₂) = l X O₂ + l X P₂ + l X G₂ := by
        rw [z₂ hX (cO₂.add cP₂) cG₂, z₂ hX cO₂ cP₂]
      rw [z₁ (cO₁.add cP₁) cG₁ ((cO₂.add cP₂).add cG₂),
        z₁ cO₁ cP₁ ((cO₂.add cP₂).add cG₂), hbreak cO₁, hbreak cP₁, hbreak cG₁]
      rw [show l P₁ O₂ = l O₂ P₁ from link_comm _ _ _,
        show l P₁ G₂ = l G₂ P₁ from link_comm _ _ _,
        show l G₁ O₂ = l O₂ G₁ from link_comm _ _ _]
      ring
    have n₁ := link_poles_le hQ hcQ cO₁ cO₂ (mul_nonneg hU (by linarith : 0 ≤ r))
      (mul_nonneg hV (by linarith : 0 ≤ r)) Oa Ob
    have n₂ := link_le hQ hcQ cO₁ cP₂ iP₂ hM (by positivity) hqb (fun t h _ => Oa t h)
    have n₃ := link_le hQ hcQ cO₂ cP₁ iP₁ hM (by positivity) hqb (fun t h _ => Ob t h)
    have n₄ := link_le hQ hcQ cO₁ cG₂ iG₂ hM (by positivity) hqb (fun t h _ => Oa t h)
    have n₅ := link_le hQ hcQ cO₂ cG₁ iG₁ hM (by positivity) hqb (fun t h _ => Ob t h)
    have n₆ := link_le hQ hcQ cG₁ cP₂ iP₂ hM (by positivity) hqb (fun t _ h => Ga t h)
    have n₇ := link_le hQ hcQ cG₂ cP₁ iP₁ hM (by positivity) hqb (fun t _ h => Gb t h)
    have nr : r ≤ r*r := by nlinarith only [mul_nonneg (by linarith : 0 ≤ r) (sub_nonneg.mpr hr)]
    have h₁ : ‖l O₁ O₂‖ ≤ U*V*(∫ t, ‖Q t‖)*(r*r) := n₁.trans_eq (by ring)
    have h₂ : ‖l O₁ P₂‖ ≤ M*U*(4*d*B)*(r*r) := n₂.trans
      ((mul_le_mul_of_nonneg_left bP₂ (by positivity)).trans_eq (by ring))
    have h₃ : ‖l O₂ P₁‖ ≤ M*V*(4*d*A)*(r*r) := n₃.trans
      ((mul_le_mul_of_nonneg_left bP₁ (by positivity)).trans_eq (by ring))
    have h₄ : ‖l O₁ G₂‖ ≤ M*U*C₂*(r*r) := n₄.trans
      ((mul_le_mul_of_nonneg_left bG₂ (by positivity)).trans
        ((show M*(U*r)*C₂ = M*U*C₂*r by ring).le.trans
          (mul_le_mul_of_nonneg_left nr (by positivity))))
    have h₅ : ‖l O₂ G₁‖ ≤ M*V*C₁*(r*r) := n₅.trans
      ((mul_le_mul_of_nonneg_left bG₁ (by positivity)).trans
        ((show M*(V*r)*C₁ = M*V*C₁*r by ring).le.trans
          (mul_le_mul_of_nonneg_left nr (by positivity))))
    have h₆ : ‖l G₁ P₂‖ ≤ M*(40*A)*(4*d*B)*(r*r) := n₆.trans
      ((mul_le_mul_of_nonneg_left bP₂ (by positivity)).trans
        ((show M*(40*A)*((4*d*B)*r) = M*(40*A)*(4*d*B)*r by ring).le.trans
          (mul_le_mul_of_nonneg_left nr (by positivity))))
    have h₇ : ‖l G₂ P₁‖ ≤ M*(40*B)*(4*d*A)*(r*r) := n₇.trans
      ((mul_le_mul_of_nonneg_left bP₁ (by positivity)).trans
        ((show M*(40*B)*((4*d*A)*r) = M*(40*B)*(4*d*A)*r by ring).le.trans
          (mul_le_mul_of_nonneg_left nr (by positivity))))
    rw [hdecomp, ← hrsq]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add h₁ h₂)) h₃)) h₄)) h₅)) h₆)) h₇) |>.trans_eq (by unfold D; ring)
  have hO : (fun T => smoothedPair a b Q T - (pairGammaTerm a b Q T+pairPrimeTerm a b Q d T))
      =O[atTop] (fun T => T^d) := by
    apply Asymptotics.IsBigO.of_bound D
    filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with T h hT
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) _)]
    exact h
  apply hO.trans_isLittleO
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT h
    exact False.elim ((mul_ne_zero (by linarith : T ≠ 0) (Real.log_pos hT).ne') h)
  · have H := tendsto_rpow_neg_atTop (sub_pos.mpr hd1)
    have hlog := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    refine (H.mul hlog).congr' ?_ |>.trans ?_
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
      have ht : 0 < T := by linarith
      change T^(-(1-d))*(Real.log T)⁻¹ = T^d/(T*Real.log T)
      rw [show -(1-d) = d + -1 by ring, Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_one]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · simp

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.smoothedPair_sub_survivors_isLittleO
