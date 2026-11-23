/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.FactorialCertificate

/-! The concrete smoothing family meets the four inputs of the
certificate's Fourier continuity theorem. -/

noncomputable section
open Complex Filter Topology MeasureTheory Set
open scoped Convolution

namespace XiPrime8845.RHTriple.CertificateSmoothing

private theorem smoothKernel_shape {e : ℝ} (he : 0 < e) :
    ∃ ψ : Plane → ℝ, Integrable ψ ∧ (∀ p, smoothingKernel e he p = (ψ p:ℂ)) ∧
      (∀ p, 0 ≤ ψ p) ∧ (∫ p, ψ p) = 1 ∧ (∀ p, ψ p ≠ 0 → ‖p‖ ≤ e/4) := by
  let b := (mollifierSeed e he).normed (volume : Measure Plane)
  have bi : Integrable b := (mollifierSeed e he).integrable_normed
  let ψ := b ⋆[ContinuousLinearMap.mul ℝ ℝ] b
  have eq (p : Plane) : smoothingKernel e he p = (ψ p:ℂ) := by
    change (∫ x, (b x:ℂ)*(b (p-x):ℂ)) = ((∫ x, b x*b (p-x)):ℝ)
    simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  refine ⟨ψ,bi.integrable_convolution _ bi,eq,fun p => ?_,?_,?_⟩
  · exact integral_nonneg fun _ => mul_nonneg
      ((mollifierSeed e he).nonneg_normed _) ((mollifierSeed e he).nonneg_normed _)
  · unfold ψ
    rw [integral_convolution _ bi bi]
    simp [b, (mollifierSeed e he).integral_normed]
  · intro p hp
    have H := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) hp
    obtain ⟨x,hx,y,hy,rfl⟩ := Set.mem_add.mp H
    rw [show Function.support b = Metric.ball 0 (e/8) from (mollifierSeed e he).support_normed_eq]
      at hx hy
    simp only [Metric.mem_ball,dist_zero_right] at hx hy
    exact (norm_add_le _ _).trans (by linarith)

private theorem smoothFrequency_eq_average {Φ : Plane → ℂ} {e : ℝ} (he : 0 < e)
    {ψ : Plane → ℝ} (hψ : ∀ q, smoothingKernel e he q = (ψ q:ℂ)) (p : Plane) :
    smoothFrequency Φ e he p = (((1-e:ℝ):ℂ)^2)⁻¹ *
      ∫ q, Φ ((1-e)⁻¹ • (p-q)) * (ψ q:ℂ) := by
  unfold smoothFrequency planeConvolution
  rw [convolution_eq_swap,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    dsimp only
    rw [ContinuousLinearMap.mul_apply', hψ, contract, mul_assoc]

private theorem contraction_norm_le_four {e : ℝ} (he : 0 < e) (he2 : e ≤ 1/2) :
    ‖(((1-e:ℝ):ℂ)^2)⁻¹‖ ≤ 4 := by
  have ha : (0:ℝ) < 1-e := by linarith
  rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg ha.le,
    ← one_div,div_le_iff₀ (by positivity)]
  nlinarith only [mul_nonneg (by linarith : 0 ≤ 1-e-1/2) (by linarith : 0 ≤ 1-e+1/2)]

theorem smoothFrequency_norm_le {Φ : Plane → ℂ} {M e : ℝ}
    (hf : ∀ p, ‖Φ p‖ ≤ M) (he : 0 < e) (he2 : e ≤ 1/2) (p : Plane) :
    ‖smoothFrequency Φ e he p‖ ≤ 4*M := by
  obtain ⟨ψ,hiψ,hψ,hnψ,hmψ,_⟩ := smoothKernel_shape he
  rw [smoothFrequency_eq_average he hψ,norm_mul]
  have H : ‖∫ q, Φ ((1-e)⁻¹ • (p-q)) * (ψ q:ℂ)‖ ≤ M := by
    refine (norm_integral_le_of_norm_le (hiψ.const_mul M)
      (Eventually.of_forall fun q => ?_)).trans ?_
    · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hnψ _)]
      exact mul_le_mul_of_nonneg_right (hf _) (hnψ _)
    · rw [integral_const_mul,hmψ,mul_one]
  exact mul_le_mul (contraction_norm_le_four he he2) H (norm_nonneg _) (by norm_num)

theorem smoothFrequency_eq_zero_outside_unit {Φ : Plane → ℂ}
    (hΦ : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2) {e : ℝ} (he : 0 < e) (he1 : e < 1)
    {p : Plane} (hp : p ∉ Metric.closedBall (0:Plane) 1) : smoothFrequency Φ e he p = 0 := by
  by_contra H
  have h := smoothFrequency_margin hΦ he he1 p H
  have h1 := abs_add_le (p.1+p.2) (-p.2)
  have h2 := abs_add_le (p.1+p.2) (-p.1)
  simp only [abs_neg,add_neg_cancel_right,show p.1+p.2+-p.1=p.2 by ring] at h1 h2
  apply hp
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,Real.norm_eq_abs,Real.norm_eq_abs]
  unfold hexGauge at h
  constructor <;> linarith

private theorem contract_distance_le {e : ℝ} (he : 0 < e) (he2 : e ≤ 1/2)
    (p q : Plane) (hq : ‖q‖ ≤ e/4) :
    ‖(1-e)⁻¹ • (p-q)-p‖ ≤ 2*e*(‖p‖+1) := by
  have ha : 0 < 1-e := by linarith
  have hh : (1-e)⁻¹ • (p-q)-p = (1-e)⁻¹ • (e • p-q) := calc
    _ = (1-e)⁻¹ • (p-q)-(1-e)⁻¹ • ((1-e) • p) := by
      rw [smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    _ = _ := by
      rw [← smul_sub]
      congr 1
      module
  rw [hh,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
  have hi : (1-e)⁻¹ ≤ 2 := by
    rw [← one_div,div_le_iff₀ ha]
    linarith
  have hs : ‖e • p-q‖ ≤ e*(‖p‖+1) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul,Real.norm_of_nonneg he.le]
    linarith
  calc
    _ ≤ 2*(e*(‖p‖+1)) := mul_le_mul hi hs (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem smoothFrequency_tendsto_pointwise {ι : Type*} {l : Filter ι}
    {Φ : Plane → ℂ} (hc : Continuous Φ) {e : ι → InteriorEpsilon}
    (hsmall : ∀ i, (e i).val ≤ 1/2) (he : Tendsto (fun i => (e i).val) l (𝓝 0))
    (p : Plane) : Tendsto (fun i => smoothedCertificate Φ (e i) p) l (𝓝 (Φ p)) := by
  classical
  choose ψ hiψ hψ hnψ hmψ hsψ using fun i => smoothKernel_shape (e i).property.1
  let A (i : ι) := ∫ q, Φ ((1-(e i).val)⁻¹ • (p-q)) * (ψ i q:ℂ)
  have hA : Tendsto A l (𝓝 (Φ p)) := by
    rw [Metric.tendsto_nhds]
    intro b hb
    obtain ⟨r,hr,hR⟩ := Metric.continuousAt_iff.mp hc.continuousAt (b/2) (by positivity)
    have hs : Tendsto (fun i => 2*(e i).val*(‖p‖+1)) l (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using (he.const_mul 2).mul_const (‖p‖+1)
    filter_upwards [hs.eventually_lt_const hr] with i hI
    have hInt : A i-Φ p = ∫ q, (Φ ((1-(e i).val)⁻¹ • (p-q))-Φ p)*(ψ i q:ℂ) := by
      have hi : Integrable (fun q => (ψ i q:ℂ)) := Complex.ofRealCLM.integrable_comp (hiψ i)
      have ht : HasCompactSupport (smoothingKernel (e i).val (e i).property.1) :=
        let B := ContinuousLinearMap.mul ℝ ℂ
        (mollifier_compact _ _).convolution B (mollifier_compact _ _)
      have hcont : Continuous (smoothingKernel (e i).val (e i).property.1) :=
        (mollifier_compact _ _).continuous_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
          (mollifier_integrable _ _).locallyIntegrable (mollifier_contDiff _ _ (n := 1)).continuous
      have hi' : Integrable (fun q => Φ ((1-(e i).val)⁻¹ • (p-q))*(ψ i q:ℂ)) := by
        simp_rw [← hψ i]
        exact Continuous.integrable_of_hasCompactSupport
          ((hc.comp (by fun_prop)).mul hcont) ht.mul_left
      simp_rw [sub_mul]
      rw [integral_sub hi' (hi.const_mul _), integral_const_mul, integral_complex_ofReal,
        hmψ i, ofReal_one,mul_one]
    rw [dist_eq_norm,hInt]
    have Hb : ‖∫ q, (Φ ((1-(e i).val)⁻¹ • (p-q))-Φ p)*(ψ i q:ℂ)‖ ≤ b/2 := by
      refine (norm_integral_le_of_norm_le ((hiψ i).const_mul (b/2))
        (Eventually.of_forall fun q => ?_)).trans ?_
      · by_cases hq : ψ i q = 0
        · simp [hq]
        · have Hq := contract_distance_le (e i).property.1 (hsmall i) p q (hsψ i q hq)
          have H := hR (show dist ((1-(e i).val)⁻¹ • (p-q)) p < r from
            (dist_eq_norm _ _).trans_lt (Hq.trans_lt hI))
          rw [dist_eq_norm] at H
          rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hnψ i q)]
          exact mul_le_mul_of_nonneg_right H.le (hnψ i q)
      · rw [integral_const_mul,hmψ i,mul_one]
    linarith
  have he' : Tendsto (fun i => (((e i).val:ℝ):ℂ)) l (𝓝 0) := by
    simpa only [ofReal_zero,Function.comp_def] using (continuous_ofReal.tendsto _).comp he
  have hscale : Tendsto (fun i => (((1-(e i).val:ℝ):ℂ)^2)⁻¹) l (𝓝 1) := by
    simpa using (((tendsto_const_nhds (x := (1:ℂ))).sub he').pow 2).inv₀ (by norm_num)
  have H := hscale.mul hA
  simpa only [one_mul,smoothedCertificate,smoothFrequency_eq_average _ (hψ _),A] using H

end XiPrime8845.RHTriple.CertificateSmoothing

#print axioms XiPrime8845.RHTriple.CertificateSmoothing.smoothFrequency_tendsto_pointwise
