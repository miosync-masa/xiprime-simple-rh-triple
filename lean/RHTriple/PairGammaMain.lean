/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.GammaPlane
import RHTriple.PairHeight

/-! The two gamma factors for independent height profiles. The scaling
is T log T, and the mixed height mass is the convolution at zero. -/

noncomputable section
open Complex MeasureTheory Filter Topology
open scoped Convolution FourierTransform

namespace XiPrime8845.RHTriple
open Zeta23

def pairHeightMass (a b : ℝ → ℂ) : ℂ := ∫ x : ℝ, a (-x)*b x

def pairGammaTerm (a b Q : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ t : ℝ, Q t * (gammaFactor (dilate a T) (Real.log T*t) *
    gammaFactor (dilate b T) (-(Real.log T*t)))

theorem pairHeightMass_eq_heightIntegral {a b : ℝ → ℂ}
    (ha : ContDiff ℝ 2 a) (hca : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hcb : HasCompactSupport b) :
    (2*Real.pi:ℂ)*pairHeightMass a b =
      ∫ r : ℝ, paperFT a r * paperFT b r := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  let k := b ⋆[B] a
  have ia := ha.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hca
  have ib := hb.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hcb
  have hk : ContDiff ℝ 2 k := hca.contDiff_convolution_right B ib.locallyIntegrable ha
  have hkc : HasCompactSupport k := hcb.convolution B hca
  have h₀ : k 0 = pairHeightMass a b := by
    unfold k pairHeightMass
    simp [convolution, B, mul_comm]
  have hft (r : ℝ) : paperFT k r = paperFT a r * paperFT b r := by
    rw [EF.paperFT_ofReal_eq_fourier, EF.paperFT_ofReal_eq_fourier, EF.paperFT_ofReal_eq_fourier]
    change 𝓕 (b ⋆[ContinuousLinearMap.mul ℂ ℂ] a) _ = _
    rw [Real.fourier_mul_convolution_eq ib ia, mul_comm]
  have hi := integral_inverseProfile hk hkc 0
  simpa only [inverseProfile, mul_zero, neg_zero, phase, ofReal_zero, exp_zero, mul_one, hft, h₀]
    using hi.symm

theorem mixedPairHeightMass (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    (2*Real.pi:ℂ)*pairHeightMass (heightSquareProfile k) k = ∫ r : ℝ, (paperFT k r)^3 := by
  rw [pairHeightMass_eq_heightIntegral (heightSquareProfile_contDiff hk hkc)
    (heightSquareProfile_compact hkc) hk hkc]
  simp_rw [paperFT_heightSquareProfile hk hkc, pow_succ _ 2]

private theorem pairGamma_rescale (a b Q : ℝ → ℂ) {T : ℝ} (hT : 1 < T) :
    pairGammaTerm a b Q T / ((T*Real.log T : ℝ):ℂ) =
      ∫ x : ℝ, Q (x/(T*Real.log T)) *
        (normalizedGamma a T (-x) * normalizedGamma b T x) := by
  let W := T*Real.log T
  have ht : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hw : 0 < W := mul_pos ht hL
  have hwc : (W:ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  let F (x : ℝ) := Q (x/W)*(normalizedGamma a T (-x) * normalizedGamma b T x)
  have hf (t : ℝ) :
      Q t*(gammaFactor (dilate a T) (Real.log T*t) *
        gammaFactor (dilate b T) (-(Real.log T*t))) = (W:ℂ)^2*F (W*t) := by
    rw [gammaFactor_dilate a ht, gammaFactor_dilate b ht]
    have H (x : ℝ) (k : ℝ → ℂ) :
        (T:ℂ)*scaledGamma k T x = (W:ℂ)*normalizedGamma k T x := by
      unfold W normalizedGamma
      push_cast
      field_simp
    rw [H, H]
    unfold F
    rw [mul_div_cancel_left₀ _ hw.ne']
    simp only [mul_neg, neg_neg, ← mul_assoc, W]
    ring
  unfold pairGammaTerm
  simp_rw [hf, integral_const_mul]
  change (W:ℂ)^2*(∫ t, F (W*t))/(W:ℂ) = ∫ x, F x
  rw [Measure.integral_comp_mul_left F W, abs_of_pos (inv_pos.mpr hw), Complex.real_smul,
    ofReal_inv]
  field_simp

theorem pairGamma_normalized_tendsto {a b Q : ℝ → ℂ}
    (ha : ContDiff ℝ 2 a) (hca : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hcb : HasCompactSupport b)
    (hQ : Continuous Q) (hcQ : HasCompactSupport Q) :
    Tendsto (fun T => pairGammaTerm a b Q T / ((T*Real.log T : ℝ):ℂ))
      atTop (𝓝 (Q 0*pairHeightMass a b)) := by
  obtain ⟨A,hA,hAb⟩ := normalizedGamma_L1 hb hcb
  obtain ⟨ea,hea,hEa⟩ := normalizedGamma_uniform ha hca
  obtain ⟨eb,heb,hEb⟩ := normalizedGamma_uniform hb hcb
  obtain ⟨M,hM₀⟩ := hcQ.isCompact.exists_bound_of_continuousOn hQ.continuousOn
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  have hQb (x : ℝ) : ‖Q x‖ ≤ C := by
    by_cases hx : x ∈ tsupport Q
    · exact (hM₀ x hx).trans (le_max_left _ _)
    · simp [image_eq_zero_of_notMem_tsupport hx, hC]
  let q (T x : ℝ) := Q (x/(T*Real.log T))
  let J (x : ℝ) := a (-x)*b x
  have hj : Integrable J := by
    have h₁ : Continuous J := (ha.continuous.comp continuous_neg).mul hb.continuous
    exact h₁.integrable_of_hasCompactSupport hcb.mul_left
  have hJ : Tendsto (fun T : ℝ => ∫ x, q T x * J x) atTop (𝓝 (Q 0*pairHeightMass a b)) := by
    unfold pairHeightMass
    rw [← integral_const_mul]
    refine tendsto_integral_filter_of_dominated_convergence (fun x => C*‖J x‖)
      (Eventually.of_forall fun T => ?_) (Eventually.of_forall fun T => ?_) (hj.norm.const_mul C) ?_
    · exact ((hQ.comp (continuous_id.div_const (T*Real.log T))).aestronglyMeasurable.mul
        hj.aestronglyMeasurable)
    · exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hQb _) (norm_nonneg _)
    · refine Eventually.of_forall fun x => ?_
      have hW : Tendsto (fun T : ℝ => T*Real.log T) atTop atTop :=
        tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
      exact ((hQ.tendsto 0).comp (tendsto_const_nhds.div_atTop hW)).mul_const _
  let D := ∫ x, ‖a (-x)‖
  have hiD : Integrable (fun x => ‖a (-x)‖) := by
    have ia : Integrable a := ha.continuous.integrable_of_hasCompactSupport hca
    simpa only [neg_one_mul] using ia.norm.comp_mul_left' (by norm_num : (-1:ℝ) ≠ 0)
  let E (T : ℝ) := (∫ x : ℝ, q T x*(normalizedGamma a T (-x)*normalizedGamma b T x)) -
    ∫ x : ℝ, q T x*J x
  have hE : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun T : ℝ => C*A*ea T+C*D*eb T) atTop (𝓝 0)
      from by simpa only [mul_zero, add_zero] using (hea.const_mul (C*A)).add (heb.const_mul (C*D)))
    filter_upwards [hEa,hEb,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with T hEaT hEbT hT hL
    let G := normalizedGamma a T
    let H := normalizedGamma b T
    obtain ⟨hiH,hHA⟩ := hAb T hT.le hL
    have hq : Continuous (q T) := hQ.comp (continuous_id.div_const _)
    have hqi : HasCompactSupport (q T) := by
      have hn : (T*Real.log T)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
      have hh := hcQ.comp_homeomorph (Homeomorph.mulLeft₀ (T*Real.log T)⁻¹ hn)
      change HasCompactSupport (fun x : ℝ => Q ((T*Real.log T)⁻¹*x)) at hh
      simpa only [q, div_eq_inv_mul] using hh
    have hG : Continuous G := normalizedGamma_continuous ha hca (by linarith)
    have hH : Continuous H := normalizedGamma_continuous hb hcb (by linarith)
    have h1 : Integrable (fun x => q T x*(G (-x)*H x)) :=
      (hq.mul ((hG.comp continuous_neg).mul hH)).integrable_of_hasCompactSupport hqi.mul_right
    have h2 : Integrable (fun x => q T x*J x) :=
      hj.mul_bdd hq.aestronglyMeasurable (Eventually.of_forall fun x => hQb _)
      |>.congr (Eventually.of_forall fun x => mul_comm _ _)
    have hm (x : ℝ) : ‖q T x*(G (-x)*H x)-q T x*J x‖ ≤
        (C*ea T)*‖H x‖ + (C*eb T)*‖a (-x)‖ := by
      have he0 : 0 ≤ ea T := (norm_nonneg _).trans (hEaT 0)
      have he1 : 0 ≤ eb T := (norm_nonneg _).trans (hEbT 0)
      rw [show q T x*(G (-x)*H x)-q T x*J x =
        q T x*((G (-x)-a (-x))*H x) + q T x*(a (-x)*(H x-b x)) by unfold J; ring]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · simp only [norm_mul, mul_assoc]
        gcongr
        · exact hQb _
        · exact hEaT _
      · simp only [norm_mul]
        rw [show ‖q T x‖*(‖a (-x)‖*‖H x-b x‖) =
          ‖q T x‖*‖H x-b x‖*‖a (-x)‖ by ring]
        gcongr
        · exact hQb _
        · exact hEbT _
    have hi := (hiH.norm.const_mul (C*ea T)).add (hiD.const_mul (C*eb T))
    unfold E
    rw [← integral_sub h1 h2]
    refine (norm_integral_le_integral_norm _).trans ((integral_mono (h1.sub h2).norm hi hm).trans ?_)
    change (∫ x, (C*ea T)*‖normalizedGamma b T x‖ + (C*eb T)*‖a (-x)‖) ≤ _
    rw [integral_add (hiH.norm.const_mul _) (hiD.const_mul _), integral_const_mul, integral_const_mul]
    change C*ea T*(∫ x, ‖H x‖) + C*eb T*D ≤ _
    calc
      _ ≤ C*ea T*A + C*eb T*D :=
        add_le_add (mul_le_mul_of_nonneg_left hHA
          (mul_nonneg hC ((norm_nonneg _).trans (hEaT 0)))) le_rfl
      _ = _ := by ring
  have HH := hE.add hJ
  rw [zero_add] at HH
  refine HH.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  rw [pairGamma_rescale _ _ _ hT]
  exact sub_add_cancel _ _

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.mixedPairHeightMass
#print axioms XiPrime8845.RHTriple.pairGamma_normalized_tendsto
