/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.HeightMajorantKernel

/-! Positive bandlimited height majorants. Convolve a flat bump with a
concentrating probability density, then divide by the enclosed mass. -/

noncomputable section
open Complex Filter Topology MeasureTheory Set
open scoped Convolution Pointwise

namespace XiPrime8845.RHTriple
open Zeta23

private theorem probability_mass_near_one {f : ℝ → ℝ} (hf : Integrable f)
    (hfi : (∫ x, f x) = 1) {a : ℝ} (ha : 0 < a) :
    ∃ R > 0, 1-a < ∫ x in Icc (-R) R, f x := by
  let W (n : ℕ) := Icc (-(n:ℝ)) (n:ℝ)
  have hW : ⋃ n, W n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := exists_nat_ge |x|
    exact mem_iUnion.mpr ⟨n,abs_le.mp hn⟩
  have H := tendsto_setIntegral_of_monotone (s := W) (fun _ => measurableSet_Icc)
    (fun _ _ h => Icc_subset_Icc (neg_le_neg (by exact_mod_cast h)) (by exact_mod_cast h))
    (hf.integrableOn (s := ⋃ n, W n))
  rw [hW, Measure.restrict_univ,hfi] at H
  obtain ⟨n,hn,hM⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (H.eventually_const_lt (show 1-a < 1 by linarith))).exists
  exact ⟨n,by exact_mod_cast (show 0<n by omega),hM⟩

private theorem paperFT_mul_modulator {k : ℝ → ℂ} (hk : Integrable k)
    {B : ℝ → ℝ} (hB : Integrable B) (t : ℝ) :
    paperFT (fun u => k u * paperFT (fun s => (B s:ℂ)) (-u:ℝ)) t =
      ∫ x, paperFT k ((t-x:ℝ):ℂ) * (B x:ℂ) := by
  let F (u x : ℝ) := (k u*(B x:ℂ))*phase (u*(t-x))
  have he (u x : ℝ) : F u x =
      (k u * ((B x:ℂ) * exp (I * (-(u:ℂ)) * x))) * exp (I * t * u) := by
    unfold F phase
    rw [show I * (↑(u*(t-x)):ℂ) = I * (-(u:ℂ)) * x + I * t * u by push_cast; ring,
      exp_add]
    ring
  have hf (u x : ℝ) : F u x =
      (k u * exp (I * ((t-x:ℝ):ℂ) * u)) * (B x:ℂ) := by
    unfold F phase
    rw [mul_comm u (t-x), Complex.ofReal_mul, ← mul_assoc]
    ring
  have hi : Integrable (fun p : ℝ × ℝ => F p.1 p.2) (volume.prod volume) := by
    have H := hk.mul_prod (Complex.ofRealCLM.integrable_comp hB)
    exact H.mul_bdd (c := 1) (continuous_phase.comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun _ => (norm_phase _).le)
  calc
    _ = ∫ u, ∫ x, F u x := by
      unfold paperFT
      apply integral_congr_ae
      filter_upwards [] with u
      rw [← integral_const_mul, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by rw [he,Complex.ofReal_neg]
    _ = ∫ x, ∫ u, F u x := integral_integral_swap hi
    _ = _ := by simp_rw [hf,integral_mul_const,paperFT]

set_option maxHeartbeats 1900000 in
theorem height_majorant_exists {e : ℝ} (he : 0 < e) :
    ∃ k : ℝ → ℂ, ∃ h : ℝ → ℝ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧
      (∀ t : ℝ, paperFT k t = (h t:ℂ)) ∧ (∀ t, 0 ≤ h t) ∧
      (∀ t ∈ Icc (1:ℝ) 2, 1 ≤ h t) ∧
      1 ≤ (∫ t, (h t)^3) ∧ (∫ t, (h t)^3) ≤ 1+e := by
  obtain ⟨q,f,hq,hqc,hfc,hfi,hF,hfn,hf1⟩ := height_probability_kernel_exists
  let a := e/(16*(1+e))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a < 1 := (div_lt_one (by positivity : 0 < 16*(1+e))).2 (by linarith)
  obtain ⟨R,hR,hA⟩ := probability_mass_near_one hfi hf1 ha
  let lam := R/a
  have hlam : 0 < lam := div_pos hR ha
  let flam (x : ℝ) := lam*f (lam*x)
  let qlam (u : ℝ) := (lam:ℂ)*dilate q lam⁻¹ u
  have hqlam : ContDiff ℝ 2 qlam := contDiff_const.mul (dilate_contDiff hq _)
  have hclam : HasCompactSupport qlam := (dilate_hasCompactSupport hqc (inv_pos.mpr hlam)).mul_left
  have hqF (x : ℝ) : paperFT qlam x = (flam x:ℂ) := by
    have H : ((x:ℂ)/((lam⁻¹:ℝ):ℂ)) = ((lam*x:ℝ):ℂ) := by push_cast; rw [div_inv_eq_mul, mul_comm]
    unfold qlam
    rw [show paperFT (fun u => (lam:ℂ)*dilate q lam⁻¹ u) x =
        (lam:ℂ)*paperFT (dilate q lam⁻¹) x by
      unfold paperFT
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)]
    rw [paperFT_dilate _ (inv_pos.mpr hlam), H, hF]
    push_cast [flam]
    rfl
  have hfilam : Integrable flam := (hfi.comp_smul hlam.ne').const_mul _
  have hfnlam (x : ℝ) : 0 ≤ flam x := mul_nonneg hlam.le (hfn _)
  have hf1lam : (∫ x, flam x) = 1 := by
    simp [flam, integral_const_mul, Measure.integral_comp_mul_left,
      abs_of_nonneg (inv_nonneg.mpr hlam.le),hf1, hlam.ne']
  let A := ∫ x in Icc (-R) R, f x
  have hAp : 0 < A := by dsimp [A]; linarith
  have hlocal : (∫ x in Icc (-a) a, flam x) = A := by
    unfold flam
    rw [integral_const_mul]
    have E : lam • Icc (-a) a = Icc (-R) R := by
      have ht : lam*a=R := div_mul_cancel₀ R ha.ne'
      ext x
      rw [mem_smul_set_iff_inv_smul_mem₀ hlam.ne',mem_Icc,mem_Icc,smul_eq_mul,
        ← div_eq_inv_mul,le_div_iff₀ hlam,div_le_iff₀ hlam, mul_comm (-a),mul_neg,ht,
        mul_comm a,ht]
    change lam * (∫ x in Icc (-a) a, f (lam • x)) = A
    rw [Measure.setIntegral_comp_smul_of_pos volume _ _ hlam, Module.finrank_self, pow_one,
      E,smul_eq_mul, ← mul_assoc,mul_inv_cancel₀ hlam.ne',one_mul]
  let B : ContDiffBump (3/2:ℝ) := ⟨1/2+a, 1/2+2*a,by positivity,by linarith⟩
  let b (x : ℝ) := B x
  have bcont : Continuous b := B.continuous
  have bi : Integrable b := bcont.integrable_of_hasCompactSupport B.hasCompactSupport
  have bn (x : ℝ) : 0 ≤ b x := B.nonneg
  have b1 (x : ℝ) : b x ≤ 1 := B.le_one
  let H (t : ℝ) := (flam ⋆[ContinuousLinearMap.mul ℝ ℝ] b) t
  have HE (t : ℝ) : H t = ∫ x, flam x*b (t-x) := rfl
  have hI (t : ℝ) : Integrable (fun x => flam x*b (t-x)) :=
    hfilam.mul_bdd (c := 1) (bcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa [Real.norm_of_nonneg (bn _)] using b1 (t-x))
  have hHn (t : ℝ) : 0 ≤ H t := integral_nonneg fun x => mul_nonneg (hfnlam x) (bn (t-x))
  have hH1 (t : ℝ) : H t ≤ 1 := by
    rw [HE,← hf1lam]
    exact integral_mono (hI t) hfilam (fun x => mul_le_of_le_one_right (hfnlam x) (b1 _))
  have hHI : Integrable H := hfilam.integrable_convolution _ bi
  have hHm : (∫ t, H t) = ∫ x, b x := by
    rw [integral_convolution _ hfilam bi, hf1lam,ContinuousLinearMap.mul_apply',one_mul]
  have hHb : (∫ t, H t) ≤ 1+4*a := by
    let U := Icc (1-2*a) (2+2*a)
    have hU : MeasurableSet U := measurableSet_Icc
    have hiU : IntegrableOn (fun _ : ℝ => (1:ℝ)) U :=
      integrableOn_const measure_Icc_lt_top.ne
    have Hle (x : ℝ) : b x ≤ U.indicator (fun _ => 1) x := by
      by_cases hx : x ∈ U
      · simpa [hx] using b1 x
      · rw [indicator_of_notMem hx]
        have Hzero : b x = 0 := by
          apply B.zero_of_le_dist
          rw [Real.dist_eq]
          rcases not_and_or.mp (show ¬ ((1-2*a ≤ x) ∧ (x ≤ 2+2*a)) from hx) with hl|hr
          · have hl' := lt_of_not_ge hl
            dsimp [B]
            linarith [neg_abs_le (x-3/2)]
          · have hr' := lt_of_not_ge hr
            dsimp [B]
            linarith [le_abs_self (x-3/2)]
        simp [Hzero]
    rw [hHm]
    calc
      _ ≤ ∫ x, U.indicator (fun _ => (1:ℝ)) x :=
        integral_mono bi (hiU.integrable_indicator hU) Hle
      _ = _ := by
        rw [integral_indicator hU]
        simp [U, show 0 ≤ (2+2*a)-(1-2*a) by linarith]
        ring
  have hHA (t : ℝ) (ht : t ∈ Icc (1:ℝ) 2) : A ≤ H t := by
    rw [← hlocal,HE]
    have ht' (x : ℝ) (hx : x ∈ Icc (-a) a) : b (t-x)=1 := by
      apply B.one_of_mem_closedBall
      rw [Metric.mem_closedBall,Real.dist_eq,abs_le]
      exact ⟨by dsimp [B]; linarith [ht.1,hx.2],by dsimp [B]; linarith [ht.2,hx.1]⟩
    calc
      _ = ∫ x in Icc (-a) a, flam x*b (t-x) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        change flam x = flam x*b (t-x)
        rw [ht' x hx,mul_one]
      _ ≤ _ := setIntegral_le_integral (hI t) (Eventually.of_forall fun x =>
        mul_nonneg (hfnlam x) (bn _))
  let kc : ℝ → ℂ := fun u => qlam u*paperFT (fun x => (b x:ℂ)) (-u:ℝ)
  have kcd : ContDiff ℝ 2 kc := hqlam.mul
    ((contDiff_real_paperFT (Complex.continuous_ofReal.comp bcont)
      (B.hasCompactSupport.comp_left Complex.ofReal_zero) 2).comp contDiff_id.neg)
  have kcc : HasCompactSupport kc := hclam.mul_right
  have hkc (t : ℝ) : paperFT kc t = (H t:ℂ) := by
    unfold kc
    rw [paperFT_mul_modulator (hqlam.continuous.integrable_of_hasCompactSupport hclam)
      (bcont.integrable_of_hasCompactSupport B.hasCompactSupport)]
    rw [HE, ← integral_sub_left_eq_self (fun x => flam x*b (t-x)) volume t,
      ← integral_complex_ofReal]
    simp only [hqF, Complex.ofReal_mul, sub_sub_self]
  let h (t : ℝ) := H t/A
  let k (u : ℝ) := (A:ℂ)⁻¹*kc u
  have hIn : Integrable (fun t => H t^3) := hHI.mono' (hHI.aestronglyMeasurable.pow 3) <|
    Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (pow_nonneg (hHn t) _)]
      calc
        H t^3 = H t * H t^2 := by ring
        _ ≤ H t * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (hHn t) (hH1 t)) (hHn t)
        _ = _ := mul_one _
  have h3i : Integrable (fun t => h t^3) := by
    simp_rw [h,div_pow]
    exact hIn.div_const _
  have hh1 (t : ℝ) (ht : t ∈ Icc (1:ℝ) 2) : 1 ≤ h t :=
    (one_le_div hAp).2 (hHA t ht)
  refine ⟨k,h,contDiff_const.mul kcd,kcc.mul_left,?_,fun t => div_nonneg (hHn t) hAp.le,
    hh1,?_,?_⟩
  · intro t
    have E : paperFT k t = (A:ℂ)⁻¹ * paperFT kc t := by
      unfold paperFT
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by dsimp [k]; ring)
    rw [E,hkc]
    change (A:ℂ)⁻¹*(H t:ℂ) = ((H t/A:ℝ):ℂ)
    push_cast
    ring
  · calc
      1 = ∫ _t in Icc (1:ℝ) 2, (1:ℝ) := by norm_num
      _ ≤ ∫ t in Icc (1:ℝ) 2, h t^3 :=
        setIntegral_mono_on (integrableOn_const (measure_Icc_lt_top.ne))
          h3i.integrableOn measurableSet_Icc (fun t ht => one_le_pow₀ (hh1 t ht))
      _ ≤ _ := setIntegral_le_integral h3i
        (Eventually.of_forall fun t => pow_nonneg (div_nonneg (hHn t) hAp.le) _)
  · have hb : (∫ t, H t^3) ≤ 1+4*a := by
      refine (integral_mono hIn hHI fun t => ?_).trans hHb
      calc
        H t^3 = H t * H t^2 := by ring
        _ ≤ H t * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (hHn t) (hH1 t)) (hHn t)
        _ = _ := mul_one _
    simp_rw [h,div_pow,integral_div]
    apply (div_le_iff₀ (pow_pos hAp _)).2
    refine hb.trans ?_
    have H1 : (1-a)^3 ≤ A^3 := pow_le_pow_left₀ (by linarith) hA.le _
    have H2 : 1-3*a ≤ (1-a)^3 := by
      nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ 3-a by linarith)]
    have H3 : a*(7+3*e) ≤ e := by
      dsimp [a]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg e]
    have H4 : 1+4*a ≤ (1+e)*(1-3*a) := by linarith
    exact H4.trans (mul_le_mul_of_nonneg_left (H2.trans H1) (by positivity))

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.height_majorant_exists
