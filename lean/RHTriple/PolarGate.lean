/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedGate
import RHTriple.PolarPlane
import RHTriple.PolarPrime

/-! Sum the nineteen pole-containing layouts of the actual explicit formula. -/

noncomputable section
open Complex MeasureTheory Filter Finset
open scoped Asymptotics

namespace XiPrime8845.RHTriple

private theorem normBound {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖Φ x‖ ≤ M := by
  obtain ⟨m, hm⟩ := hΦc.isCompact.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max m 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport Φ
  · exact (hm x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

private theorem scale_envelope {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ b, 0 ≤ f b)
    {L : ℝ} (hL : 1 ≤ L) :
    Integrable (fun u => f (L*u)) ∧ (∫ u, f (L*u)) ≤ ∫ u, f u := by
  have hl : 0 < L := by linarith
  refine ⟨hf.comp_mul_left' hl.ne', ?_⟩
  rw [Measure.integral_comp_mul_left f, smul_eq_mul, abs_of_pos (inv_pos.mpr hl)]
  exact mul_le_of_le_one_left (integral_nonneg hf0) (inv_le_one_of_one_le₀ hL)

private theorem log_floor_le_height {T d : ℝ} (hT : 1 ≤ T) (hd : d ≤ 1) :
    Real.log (⌊T^d⌋₊ : ℕ) ≤ Real.log T := by
  have ht : 0 < T := by linarith
  by_cases hn : ⌊T^d⌋₊ = 0
  · simp [hn, Real.log_nonneg hT]
  · have hn' : 0 < (⌊T^d⌋₊ : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    exact (Real.log_le_log hn' (Nat.floor_le (Real.rpow_nonneg ht.le _))).trans
      (by rw [Real.log_rpow ht]; nlinarith only [mul_nonneg (Real.log_nonneg hT) (sub_nonneg.mpr hd)])

private theorem dampedEnvelope {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, k x ≠ 0 → |x| ≤ R) {d : ℝ} (hd : d ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T ≥ 1, 1 ≤ Real.log T → ∀ j : Fin 3,
      ∃ f : ℝ → ℝ, Integrable f ∧ (∀ u, 0 ≤ f u) ∧
      (∫ u, f u) ≤ K*(1+Real.log T)^2 ∧
      ∀ u, u ∈ Set.Icc (-2:ℝ) 2 →
        Real.exp (-|Real.log T*u|/2) * ‖factors (dilate k T) (d*Real.log T) j (Real.log T*u)‖ ≤ f u := by
  obtain ⟨G, hG, hGb⟩ := gammaFactor_dilate_L1 hk hkc
  let W := Real.exp (R/2)*(∫ b, ‖k b‖)
  have hW : 0 ≤ W := by unfold W; positivity
  let D := 2*Real.exp (R/2)*(∫ b, ‖k b‖)
  have hD : 0 ≤ D := by unfold D; positivity
  let K := 4*D+2*W+G
  refine ⟨K, by unfold K; positivity, fun T hT hL j => ?_⟩
  have ht : 0 < T := by linarith
  let L := Real.log T
  have hl1 : 1 ≤ L := hL
  have hl : 0 ≤ L := by linarith
  have base : 1 ≤ (1+L)^2 := by nlinarith
  have sq : 1+L ≤ (1+L)^2 := by nlinarith
  have hkI : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  fin_cases j
  · let f : ℝ → ℝ := (Set.Icc (-2) 2).indicator (fun _ => D)
    have hf : Integrable f := (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    refine ⟨f, hf, fun u => Set.indicator_nonneg (fun _ _ => hD) _, ?_, ?_⟩
    · have H : (∫ u, f u) = 4*D := by
        unfold f
        rw [integral_indicator measurableSet_Icc, setIntegral_const, Measure.real, Real.volume_Icc]
        rw [ENNReal.toReal_ofReal (show 0 ≤ (2:ℝ) - -2 by norm_num), smul_eq_mul]
        ring
      rw [H]
      calc
        _ ≤ K := by unfold K; linarith
        _ ≤ _ := by exact le_mul_of_one_le_right (by unfold K; positivity) base
    · intro u hu
      change Real.exp (-|L*u|/2)*‖poleFactor (dilate k T) (L*u)‖ ≤ f u
      rw [show f u = D from Set.indicator_of_mem hu _]
      calc
        _ ≤ Real.exp (-|L*u|/2)*(D*Real.exp (|L*u|/2)) := by
          gcongr
          exact scaledPoleFactor_norm_le hkI hR hs hT _
        _ = D*(Real.exp (-|L*u|/2)*Real.exp (|L*u|/2)) := by ring
        _ = D := by rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
  · let N := ⌊T^d⌋₊
    let P (s : Bool) (b : ℝ) := Real.exp (-|b|/2)*‖signedPrimeFactor k T N s b‖
    have hP (s : Bool) := dampedSignedPrimeFactor_L1 hkI hs hT N s
    have hPL (s : Bool) := scale_envelope (hP s).1 (fun _ => by positivity) hL
    refine ⟨fun u => P false (L*u)+P true (L*u), (hPL false).1.add (hPL true).1,
      fun u => by unfold P; positivity, ?_, ?_⟩
    · have hlog : Real.log (N:ℝ) ≤ L := log_floor_le_height hT hd
      have hlog0 : 0 ≤ Real.log (N:ℝ) := Real.log_natCast_nonneg N
      have hp (s : Bool) : (∫ u, P s (L*u)) ≤ W*(1+L)^2 := by
        refine (hPL s).2.trans ((hP s).2.trans ?_)
        change W * (Real.log (N:ℝ)*(1+Real.log (N:ℝ))) ≤ _
        have hplus : 0 ≤ 1+L := by linarith
        have hsmall : 0 ≤ 1+Real.log (N:ℝ) := by linarith
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hlog.trans (by linarith)) (by linarith only [hlog]) hsmall hplus) hW
      rw [integral_add (hPL false).1 (hPL true).1]
      calc
        _ ≤ (2*W)*(1+L)^2 := by linarith only [hp false, hp true]
        _ ≤ K*(1+L)^2 := mul_le_mul_of_nonneg_right (by unfold K; linarith) (by positivity)
    · intro u _
      change Real.exp (-|L*u|/2)*‖primeFactor (dilate k T) (d*Real.log T) (L*u)‖ ≤ _
      rw [primeFactor_eq_signed k ht, norm_neg]
      change _ ≤ Real.exp (-|L*u|/2)*‖signedPrimeFactor k T N false (L*u)‖ +
        Real.exp (-|L*u|/2)*‖signedPrimeFactor k T N true (L*u)‖
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_nonneg _)
  · let Q (b : ℝ) := ‖gammaFactor (dilate k T) b‖
    have hQ := hGb hT
    have hQL := scale_envelope hQ.1 (fun _ => norm_nonneg _) hL
    refine ⟨fun u => Q (L*u), hQL.1, fun _ => norm_nonneg _, ?_, ?_⟩
    · calc
        _ ≤ G*(1+L) := hQL.2.trans hQ.2
        _ ≤ G*(1+L)^2 := mul_le_mul_of_nonneg_left sq hG
        _ ≤ K*(1+L)^2 := mul_le_mul_of_nonneg_right (by unfold K; linarith) (by positivity)
    · intro u _
      change Real.exp (-|L*u|/2)*Q (L*u) ≤ Q (L*u)
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) (by norm_num)))

theorem pole_last_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) (i j : Fin 3) :
    (fun T => mixedEFIntegral k Φ (1-η/4) T i j 0) =o[atTop] (fun T => T*Real.log T) := by
  let d := 1-η/4
  have hd : d ≤ 1 := by unfold d; linarith
  obtain ⟨R₀, hs₀⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs (b : ℝ) (hb : k b ≠ 0) : |b| ≤ R := (hs₀ b hb).trans (le_max_left _ _)
  obtain ⟨M,hM,hMb⟩ := normBound hΦ hΦc
  obtain ⟨K,hK,E⟩ := dampedEnvelope hk hkc hR hs hd
  let D := 2*Real.exp (R/2)*(∫ b, ‖k b‖)
  apply littleO_height_power_polylog hη (show 0 ≤ M*D*K^2 by unfold D; positivity)
  filter_upwards [eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hL
  have ht : 0 < T := by linarith
  obtain ⟨f,hf,hf0,hfb,hfe⟩ := E T hT hL i
  obtain ⟨g,hg,hg0,hgb,hge⟩ := E T hT hL j
  have hc (a : Fin 3) := factors_continuous (dilate_contDiff hk T) (dilate_hasCompactSupport hkc ht)
    (d*Real.log T) a
  have hc₀ (x : ℝ × ℝ) (hx : Φ x ≠ 0) : x.1 ∈ Set.Icc (-2:ℝ) 2 := by
    apply abs_le.mp
    linarith only [hhex x hx, hη, abs_nonneg x.2, abs_nonneg (x.1+x.2)]
  have hc₁ (x : ℝ × ℝ) (hx : Φ x ≠ 0) : x.2 ∈ Set.Icc (-2:ℝ) 2 := by
    apply abs_le.mp
    linarith only [hhex x hx, hη, abs_nonneg x.1, abs_nonneg (x.1+x.2)]
  have H := pole_last_plane_bound hk hkc hΦ hΦc (hc i) (hc j) hR hs hM hMb hT hhex
    hf hg hf0 hg0 (fun x hx => hfe x.1 (hc₀ x hx)) (fun x hx => hge x.2 (hc₁ x hx))
  change ‖mixedEFIntegral k Φ d T i j 0‖ ≤ (M*D*K^2)*T^(1-η/2)*(1+Real.log T)^4
  calc
    _ ≤ M*D*T^(1-η/2)*((∫ b, f b)*(∫ b, g b)) := H
    _ ≤ M*D*T^(1-η/2)*(K*(1+Real.log T)^2*(K*(1+Real.log T)^2)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul hfb hgb (integral_nonneg hg0) (by positivity))
        (by unfold D; positivity)
    _ = _ := by ring

private theorem hex_swap01 {Φ : ℝ × ℝ → ℂ} {η : ℝ}
    (h : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    ∀ x : ℝ × ℝ, (Φ ∘ swap01) x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η := by
  intro x hx
  have hx' := h (swap01 x) hx
  change |x.2|+|x.1|+|x.2+x.1| ≤ _ at hx'
  simpa only [add_comm x.2 x.1, add_comm |x.2| |x.1|] using hx'

private theorem hex_swap12 {Φ : ℝ × ℝ → ℂ} {η : ℝ}
    (h : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    ∀ x : ℝ × ℝ, (Φ ∘ swap12) x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η := by
  intro x hx
  have hx' := h (swap12 x) hx
  change |x.1|+|-(x.1+x.2)|+|x.1+ -(x.1+x.2)| ≤ _ at hx'
  rw [show x.1+ -(x.1+x.2) = -x.2 by ring, abs_neg, abs_neg] at hx'
  linarith only [hx']

theorem any_pole_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η)
    (i j l : Fin 3) (hp : i = 0 ∨ j = 0 ∨ l = 0) :
    (fun T => mixedEFIntegral k Φ (1-η/4) T i j l) =o[atTop] (fun T => T*Real.log T) := by
  let d := 1-η/4
  rcases hp with rfl | rfl | rfl
  · have h01 := hΦ.comp swap01.continuous
    have h01c := hΦc.comp_homeomorph swap01
    refine (pole_last_isLittleO hk hkc (h01.comp swap12.continuous)
      (h01c.comp_homeomorph swap12) hη (hex_swap12 (hex_swap01 hhex)) j l).congr'
      ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact ((mixedEF_swap01 k Φ d T 0 j l).trans
      (mixedEF_swap12 hk hkc h01 h01c d hT j 0 l)).symm
  · refine (pole_last_isLittleO hk hkc (hΦ.comp swap12.continuous)
      (hΦc.comp_homeomorph swap12) hη (hex_swap12 hhex) i l).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact (mixedEF_swap12 hk hkc hΦ hΦc d hT i 0 l).symm
  · exact pole_last_isLittleO hk hkc hΦ hΦc hη hhex i j

theorem polarRemainder_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    (fun T => polarRemainder k Φ (1-η/4) T) =o[atTop] (fun T => T*Real.log T) := by
  unfold polarRemainder
  apply Asymptotics.IsLittleO.fun_sum
  intro js _
  by_cases h : js.1.1 = 0 ∨ js.1.2 = 0 ∨ js.2 = 0
  · simpa only [if_pos h] using any_pole_isLittleO hk hkc hΦ hΦc hη hhex _ _ _ h
  · simp [h]

/-- Remove the mixed and polar error in the actual zero-side identity. The
all-prime factor is explicit here; its signed-sum assembly is a separate step. -/
theorem smoothedTriple_sub_survivors_isLittleO (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    let d := 1-η/4
    (fun T => smoothedTriple k Φ T -
      (mixedEFIntegral k Φ d T 2 2 2 + mixedEFIntegral k Φ d T 1 1 1 +
        retainedPrimePairs k Φ d T)) =o[atTop] (fun T => T*Real.log T) := by
  let d := 1-η/4
  refine ((polarRemainder_isLittleO hk hkc hΦ hΦc hη hhex).add
    (mixedRemainder_isLittleO hk hkc hΦ hΦc hη hη1)).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [smoothedTriple_eventually_mixed_split hRH hk hkc hΦ hΦc hη hhex] with T hT
  change polarRemainder k Φ d T + mixedRemainder k Φ d T = smoothedTriple k Φ T - _
  rw [hT]
  abel

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pole_last_isLittleO
#print axioms XiPrime8845.RHTriple.any_pole_isLittleO
#print axioms XiPrime8845.RHTriple.polarRemainder_isLittleO
#print axioms XiPrime8845.RHTriple.smoothedTriple_sub_survivors_isLittleO
