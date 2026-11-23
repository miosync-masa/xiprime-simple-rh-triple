/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.GammaSeries

/-! The geometric majorant supplied by the actual ζ gamma kernel. -/

noncomputable section
open Complex MeasureTheory Filter

namespace XiPrime8845.RHTriple

theorem integral_expWeight_tail_bound {k : ℝ → ℂ} (hki : Integrable k)
    {R x a : ℝ} (ha : 0 < a) (hR : ∀ u, k u ≠ 0 → |u| ≤ R) :
    ‖∫ u, shift k (-x) u * expWeight a u‖ ≤
      (∫ u, ‖k u‖) * Real.exp (-a * (|x|-R)) := by
  have hshift : Integrable (shift k (-x)) := by
    change Integrable (fun u : ℝ => k (u - -x))
    simpa only [sub_neg_eq_add] using hki.comp_add_right x
  have hE : Continuous (expWeight a) := by unfold expWeight; fun_prop
  have hEb : ∀ u, ‖expWeight a u‖ ≤ 1 := by
    intro u
    rw [expWeight, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])
  have hi := hshift.mul_bdd (c := 1) hE.aestronglyMeasurable (Eventually.of_forall hEb)
  have hpoint (u : ℝ) : ‖shift k (-x) u * expWeight a u‖ ≤
      ‖shift k (-x) u‖ * Real.exp (-a*(|x|-R)) := by
    by_cases hz : shift k (-x) u = 0
    · simp [hz]
    have hux : |u+x| ≤ R := hR _ (by simpa [shift, sub_neg_eq_add] using hz)
    have hx : |x| ≤ |u+x|+|u| := by
      simpa only [add_sub_cancel_left] using abs_sub (u+x) u
    rw [norm_mul, expWeight, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr ha.le)
  calc
    _ ≤ ∫ u, ‖shift k (-x) u * expWeight a u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, ‖shift k (-x) u‖ * Real.exp (-a*(|x|-R)) :=
      integral_mono hi.norm (hshift.norm.mul_const _) hpoint
    _ = _ := by
      rw [integral_mul_const]
      change (∫ u, ‖k (u - -x)‖) * _ = _
      simp_rw [sub_neg_eq_add]
      rw [integral_add_right_eq_self (fun u => ‖k u‖) x]

theorem scaledGamma_tail_geometric {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {R T x : ℝ} (hT : 0 < T) (hR : ∀ u, k u ≠ 0 → |u| ≤ R) (hx : R < |x|) :
    ‖scaledGamma k T x‖ ≤ (∫ u, ‖k u‖) *
      (Real.exp (-(|x|-R)/(2*T)) / (T * (1 - Real.exp (-2*(|x|-R)/T)))) := by
  let d := |x|-R
  let A := ∫ u, ‖k u‖
  let q := Real.exp (-2*d/T)
  let B := A * Real.exp (-d/(2*T))
  have hd : 0 < d := by dsimp [d]; linarith
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by
    have hh : 0 < 2*d/T := by positivity
    rw [neg_mul, neg_div]
    exact neg_lt_zero.mpr hh)
  have hz : k x = 0 := by by_contra hn; exact (not_le_of_gt hx) (hR _ hn)
  let F n := ∫ u, shift k (-x) u * expWeight (gammaSpacing n / T) u
  have hF : HasSum F (-(T : ℂ) * scaledGamma k T x) := scaledGamma_eq_series hk hkc hT hz
  have hm (n : ℕ) : ‖F n‖ ≤ B * q^n := by
    apply (integral_expWeight_tail_bound (hk.continuous.integrable_of_hasCompactSupport hkc)
      (div_pos (gammaSpacing_pos n) hT) hR).trans_eq
    change A * Real.exp (-(gammaSpacing n/T)*d) = B*q^n
    unfold B q gammaSpacing
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left B
  have hnorm := Summable.of_nonneg_of_le (fun n => norm_nonneg (F n)) hm hs
  have hh : ‖-(T : ℂ) * scaledGamma k T x‖ ≤ B * (1-q)⁻¹ := calc
    _ = ‖∑' n, F n‖ := by rw [hF.tsum_eq]
    _ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, B * q^n := hnorm.tsum_le_tsum hm hs
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hT.le, mul_comm T, ← le_div_iff₀ hT] at hh
  apply hh.trans_eq
  change B * (1-q)⁻¹ / T = A * (Real.exp (-d/(2*T))/(T*(1-q)))
  unfold B
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem scaledGamma_tail {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {R T x : ℝ} (hT : 0 < T) (hR : ∀ u, k u ≠ 0 → |u| ≤ R) (hx : R < |x|) :
    ‖scaledGamma k T x‖ ≤ 5 * (∫ u, ‖k u‖) *
      (Real.exp (-(|x|-R)/(4*T)) / (|x|-R)) := by
  let d := |x|-R
  have hd : 0 < d := by dsimp [d]; linarith
  let y := 2*d/T
  have hy : 0 < y := by unfold y; positivity
  have h1 : 0 < 1 - Real.exp (-y) := sub_pos.mpr (Real.exp_lt_one_iff.2 (neg_lt_zero.mpr hy))
  have he : (1+y) * Real.exp (-y) ≤ 1 := calc
    _ ≤ Real.exp y * Real.exp (-y) := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp y]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hq : (1 - Real.exp (-y))⁻¹ ≤ 1 + y⁻¹ := by
    rw [← one_div, div_le_iff₀ h1]
    have hy' := inv_pos.mpr hy
    have hh := mul_le_mul_of_nonneg_right he hy'.le
    rw [show (1+y) * Real.exp (-y) * y⁻¹ = (1+y⁻¹) * Real.exp (-y) by field_simp; ring] at hh
    nlinarith
  let w := d/(4*T)
  have hw : 0 < w := by unfold w; positivity
  have hwE : w * Real.exp (-w) ≤ 1 := calc
    _ ≤ Real.exp w * Real.exp (-w) := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp w]) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hwOne : Real.exp (-w) ≤ 1 := (Real.exp_lt_one_iff.2 (neg_lt_zero.mpr hw)).le
  have hM : Real.exp (-d/(2*T)) / (T * (1-Real.exp (-y))) ≤
      5 * (Real.exp (-w)/d) := by
    calc
      _ = (Real.exp (-d/(2*T))/T) * (1-Real.exp (-y))⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (Real.exp (-d/(2*T))/T) * (1+y⁻¹) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (Real.exp (-w)/d) * (4*(w*Real.exp (-w)) + Real.exp (-w)/2) := by
        rw [show -d/(2*T) = -w + -w by unfold w; ring, Real.exp_add]
        unfold w y
        field_simp
      _ ≤ _ := by
        rw [mul_comm 5]
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have H := scaledGamma_tail_geometric hk hkc hT hR hx
  refine H.trans ?_
  have hyneg : -2*(|x|-R)/T = -y := by unfold y d; ring
  have hwneg : -(|x|-R)/(4*T) = -w := by unfold w d; ring
  rw [hyneg, hwneg]
  change _ * (Real.exp (-d/(2*T))/(T*(1-Real.exp (-y)))) ≤ 5 * _ * (Real.exp (-w)/d)
  rw [mul_comm 5, mul_assoc]
  exact mul_le_mul_of_nonneg_left hM (integral_nonneg fun _ => norm_nonneg _)

open Set in
private def tailEnvelope (T : ℝ) : ℝ → ℝ :=
  (Ioi 1).indicator fun d => Real.exp (-d/(4*T))/d

open Set in
private theorem tailEnvelope_bound {T : ℝ} (hT : 1 ≤ T) :
    Integrable (tailEnvelope T) ∧ (∫ d, tailEnvelope T d) ≤ Real.log T + 4 := by
  let E : ℝ → ℝ := fun d => Real.exp (-d/(4*T))/d
  let a : ℝ := -(1/(4*T))
  have hT0 : 0 < T := by linarith
  have ha : a < 0 := by dsimp only [a]; exact neg_lt_zero.mpr (by positivity)
  have hE : ContinuousOn E (Ioi 0) := by
    unfold E
    exact (show Continuous (fun d : ℝ => Real.exp (-d/(4*T))) by fun_prop).continuousOn.div
      continuous_id.continuousOn (fun d hd => ne_of_gt (mem_Ioi.mp hd))
  have hm : IntegrableOn E (Ioc 1 T) := by
    have hc : ContinuousOn E (Icc 1 T) := hE.mono (fun d hd => mem_Ioi.mpr (by linarith [hd.1]))
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hf := (integrableOn_exp_mul_Ioi ha T).mul_const (1/T)
  have hpt (d : ℝ) (hd : T < d) : E d ≤ Real.exp (a*d) * (1/T) := by
    have hd0 := hT0.trans hd
    unfold E
    rw [show -d/(4*T) = a*d by dsimp [a]; ring, div_eq_mul_inv, one_div]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hT0 hd.le) (Real.exp_pos _).le
  have hfi : IntegrableOn E (Ioi T) := by
    refine hf.mono' ((hE.mono (Ioi_subset_Ioi hT0.le)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun d hd => ?_)
    have hd0 : 0 < d := hT0.trans (mem_Ioi.mp hd)
    rw [Real.norm_of_nonneg (show 0 ≤ E d from by unfold E; positivity)]
    exact hpt d (mem_Ioi.mp hd)
  have hI : IntegrableOn E (Ioi 1) := (Ioc_union_Ioi_eq_Ioi hT) ▸ hm.union hfi
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).2 hI, ?_⟩
  have hl : (∫ d in Ioc 1 T, E d) ≤ Real.log T := by
    have hv : (0 : ℝ) ∉ uIcc (1:ℝ) T := by rw [uIcc_of_le hT]; simp
    have hInt : IntervalIntegrable (fun d : ℝ => d⁻¹) volume 1 T :=
      ((continuousOn_inv₀.mono (fun d hd => fun hh => hv (hh ▸ hd))) :
        ContinuousOn (fun d : ℝ => d⁻¹) (uIcc 1 T)).intervalIntegrable
    have heq : (∫ d in Ioc 1 T, d⁻¹) = Real.log T := by
      rw [← intervalIntegral.integral_of_le hT, integral_inv hv, div_one]
    rw [← heq]
    apply setIntegral_mono_on hm hInt.1 measurableSet_Ioc
    intro d hd
    unfold E
    have hd0 : 0 < d := lt_trans zero_lt_one hd.1
    rw [div_eq_mul_inv]
    apply mul_le_of_le_one_left (inv_pos.mpr hd0).le
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  have hfar : (∫ d in Ioi T, E d) ≤ 4 := calc
    _ ≤ ∫ d in Ioi T, Real.exp (a*d) * (1/T) :=
      setIntegral_mono_on hfi hf measurableSet_Ioi (fun d hd => hpt d (mem_Ioi.mp hd))
    _ = 4 * Real.exp (-1/4) := by
      rw [integral_mul_const, integral_exp_mul_Ioi ha]
      have hval : a*T = -1/4 := by unfold a; field_simp
      rw [hval]
      unfold a
      field_simp
    _ ≤ 4 := by linarith [Real.exp_le_one_iff.mpr (show -(1:ℝ)/4 ≤ 0 by norm_num)]
  rw [tailEnvelope, integral_indicator measurableSet_Ioi, ← Ioc_union_Ioi_eq_Ioi hT,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hm hfi]
  exact add_le_add hl hfar

open Set in
theorem scaledGamma_L1 {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ≥ 1, Integrable (scaledGamma k T) ∧
      (∫ x, ‖scaledGamma k T x‖) ≤ C*(1+Real.log T) := by
  obtain ⟨M, hM, hsup⟩ := scaledGamma_uniform_log hk hkc
  obtain ⟨R₀, hR₀⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  let R := max 0 R₀
  have hR0 : 0 ≤ R := le_max_left _ _
  have hR (u : ℝ) (hu : k u ≠ 0) : |u| ≤ R := (hR₀ u hu).trans (le_max_right _ _)
  let S := R+1
  have hS : 0 < S := by dsimp [S]; linarith
  let A := 5 * ∫ u, ‖k u‖
  have hA : 0 ≤ A := by positivity
  refine ⟨2*S*M+8*A, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hcont : Continuous (scaledGamma k T) := by
    have hcg := gammaFactor_continuous (gammaWeight_integrable
      (dilate_contDiff hk T) (dilate_hasCompactSupport hkc hT0))
    have hscale (x : ℝ) : scaledGamma k T x = (T:ℂ)⁻¹ * gammaFactor (dilate k T) (-(x/T)) := by
      rw [gammaFactor_dilate k hT0, show -(T * -(x/T)) = x by field_simp,
        ← mul_assoc, inv_mul_cancel₀ (show (T:ℂ) ≠ 0 by exact_mod_cast hT0.ne'), one_mul]
    rw [funext hscale]
    exact continuous_const.mul (hcg.comp ((continuous_id.div_const T).neg))
  let C₀ := M*(1+Real.log T)
  let f₀ := (Icc (-S) S).indicator (fun _ => C₀)
  let fp := fun x => tailEnvelope T (x-R)
  let fm := fun x => tailEnvelope T (-x-R)
  have hEnv := tailEnvelope_bound hT
  have hi₀ : Integrable f₀ := (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hip : Integrable fp := by simpa [fp, sub_eq_add_neg] using hEnv.1.comp_add_right (-R)
  have him : Integrable fm := by
    have hp := hip.comp_neg
    exact hp
  have hpt (x : ℝ) : ‖scaledGamma k T x‖ ≤ f₀ x + A*fp x + A*fm x := by
    by_cases hxs : |x| ≤ S
    · have hp : ¬(1 < x-R) := by linarith [(abs_le.mp hxs).2]
      have hm : ¬(1 < -x-R) := by linarith [(abs_le.mp hxs).1]
      simpa [f₀, fp, fm, abs_le.mp hxs, tailEnvelope, hp, hm] using hsup T hT x
    · have hx := lt_of_not_ge hxs
      have h₀ : x ∉ Icc (-S) S := fun h => hxs (abs_le.mpr h)
      have ht := scaledGamma_tail hk hkc hT0 hR (show R < |x| by dsimp [S] at hx; linarith)
      rcases le_or_gt 0 x with hpos | hneg
      · rw [abs_of_nonneg hpos] at hx ht
        have hp : 1 < x-R := by dsimp [S] at hx; linarith
        have hm : ¬(1 < -x-R) := by linarith
        simpa [f₀, tailEnvelope, fp, fm, h₀, hp, hm, A] using ht
      · rw [abs_of_neg hneg] at hx ht
        have hm : 1 < -x-R := by dsimp [S] at hx; linarith
        have hp : ¬(1 < x-R) := by linarith
        simpa [f₀, tailEnvelope, fp, fm, h₀, hp, hm, A] using ht
  have hDom := (hi₀.add (hip.const_mul A)).add (him.const_mul A)
  have hInt := hDom.mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)
  refine ⟨hInt, (integral_mono hInt.norm hDom hpt).trans ?_⟩
  have hf₀ : (∫ x, f₀ x) = 2*S*C₀ := by
    unfold f₀
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (show 0 ≤ S - -S by linarith), smul_eq_mul]
    ring
  have hfp : (∫ x, fp x) = ∫ d, tailEnvelope T d := by
    simpa [fp, sub_eq_add_neg] using integral_add_right_eq_self (tailEnvelope T) (-R)
  have hfm : (∫ x, fm x) = ∫ d, tailEnvelope T d := by
    rw [← hfp]; exact integral_neg_eq_self fp volume
  rw [integral_add' (hi₀.add (hip.const_mul A)) (him.const_mul A),
    integral_add' hi₀ (hip.const_mul A), integral_const_mul, integral_const_mul, hf₀, hfp, hfm]
  have hI := mul_le_mul_of_nonneg_left hEnv.2 hA
  dsimp [C₀]
  nlinarith [mul_nonneg hA hlog]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.scaledGamma_tail_geometric
#print axioms XiPrime8845.RHTriple.scaledGamma_tail
#print axioms XiPrime8845.RHTriple.scaledGamma_L1
