/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MainPlane

/-! Pass the uniform gamma approximation through the plane integral.
The two unchanged factors are bounded in L¹, in independent coordinates. -/

noncomputable section
open Complex MeasureTheory Filter Topology

namespace XiPrime8845.RHTriple

theorem normalizedGamma_continuous {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {T : ℝ} (ht : 0 < T) :
    Continuous (normalizedGamma k T) := by
  have hG := gammaFactor_continuous (gammaWeight_integrable (dilate_contDiff hk T)
    (dilate_hasCompactSupport hkc ht))
  have he (x : ℝ) : normalizedGamma k T x =
      ((T:ℂ)⁻¹ * gammaFactor (dilate k T) (-(x/T))) / (Real.log T : ℂ) := by
    rw [gammaFactor_dilate k ht, show -(T * -(x/T)) = x by field_simp,
      ← mul_assoc, inv_mul_cancel₀ (show (T:ℂ) ≠ 0 by exact_mod_cast ht.ne'), one_mul]
    rfl
  rw [funext he]
  exact (continuous_const.mul (hG.comp ((continuous_id.div_const T).neg))).div_const _

theorem normalizedGamma_L1 {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ≥ 1, 1 ≤ Real.log T →
      Integrable (normalizedGamma k T) ∧ (∫ x, ‖normalizedGamma k T x‖) ≤ C := by
  obtain ⟨C,hC,hb⟩ := scaledGamma_L1 hk hkc
  refine ⟨2*C, by positivity, fun T ht hL => ⟨(hb T ht).1.div_const _, ?_⟩⟩
  have hL0 : 0 < Real.log T := by linarith
  unfold normalizedGamma
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hL0.le]
  rw [integral_div, div_le_iff₀ hL0]
  exact (hb T ht).2.trans (by nlinarith only [mul_nonneg hC (sub_nonneg.mpr hL)])

private def planeIntegrand (Φ : ℝ × ℝ → ℂ) (A B C : ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  Φ x * (A x.1 * B x.2 * C (-(x.1+x.2)))

theorem planeProduct_telescoping {Φ : ℝ × ℝ → ℂ} {A B : ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hA : Continuous A) (hB : Continuous B) :
    planeProduct Φ A A A - planeProduct Φ B B B =
      (planeProduct Φ (A-B) A A + planeProduct Φ B (A-B) A) + planeProduct Φ B B (A-B) := by
  have hi {P Q R : ℝ → ℂ} (hp : Continuous P) (hq : Continuous Q) (hr : Continuous R) :
      Integrable (planeIntegrand Φ P Q R) :=
    planeProduct_integrable hΦ hΦc hp hq hr
  have hAB : Continuous (A-B) := hA.sub hB
  unfold planeProduct
  change ((∫ x, planeIntegrand Φ A A A x) - ∫ x, planeIntegrand Φ B B B x) =
    ((∫ x, planeIntegrand Φ (A-B) A A x) + ∫ x, planeIntegrand Φ B (A-B) A x) +
      ∫ x, planeIntegrand Φ B B (A-B) x
  have hsum : (∫ x, (planeIntegrand Φ (A-B) A A x + planeIntegrand Φ B (A-B) A x) +
      planeIntegrand Φ B B (A-B) x) =
      (∫ x, planeIntegrand Φ (A-B) A A x + planeIntegrand Φ B (A-B) A x) +
        ∫ x, planeIntegrand Φ B B (A-B) x :=
    integral_add ((hi hAB hA hA).add (hi hB hAB hA)) (hi hB hB hAB)
  rw [← integral_sub (hi hA hA hA) (hi hB hB hB),
    ← integral_add (hi hAB hA hA) (hi hB hAB hA), ← hsum]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [planeIntegrand, Pi.sub_apply]
  ring

/-- A moving uniformly bounded test is allowed; no bound on its derivatives
or support radii is used in replacing the three normalized gamma kernels. -/
theorem normalizedGamma_plane_replace {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {Ψ : ℝ → (ℝ × ℝ) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hΨ : ∀ᶠ T in atTop, Continuous (Ψ T) ∧ HasCompactSupport (Ψ T) ∧ ∀ x, ‖Ψ T x‖ ≤ M) :
    Tendsto (fun T => planeProduct (Ψ T) (normalizedGamma k T) (normalizedGamma k T)
      (normalizedGamma k T) - planeProduct (Ψ T) k k k) atTop (𝓝 0) := by
  obtain ⟨e,he,hE⟩ := normalizedGamma_uniform hk hkc
  obtain ⟨C,hC,hG⟩ := normalizedGamma_L1 hk hkc
  have hki := hk.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc
  let J := ∫ x, ‖k x‖
  let K := C+J
  have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  have hlim : Tendsto (fun T => 3*M*K^2*e T) atTop (𝓝 0) := by simpa using he.const_mul (3*M*K^2)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hΨ,hE,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T ⟨hc,hcc,hb⟩ hE' hT hL
  let G := normalizedGamma k T
  let E := G-k
  have hGc : Continuous G := normalizedGamma_continuous hk hkc (by linarith)
  have hEc : Continuous E := hGc.sub hk.continuous
  have hEb (x : ℝ) : ‖E x‖ ≤ e T := hE' x
  have he0 : 0 ≤ e T := (norm_nonneg _).trans (hEb 0)
  obtain ⟨hGi,hGb⟩ := hG T hT hL
  have hGl : (∫ x, ‖G x‖) ≤ K := hGb.trans (by unfold K; linarith)
  have hkl : (∫ x, ‖k x‖) ≤ K := by unfold K; linarith
  have bnd {F : (ℝ × ℝ) → ℂ} {P Q : ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
      (hFb : ∀ x, ‖F x‖ ≤ M) (hP : Continuous P) (hQ : Continuous Q)
      (hPi : Integrable P) (hQi : Integrable Q)
      (hPb : (∫ x, ‖P x‖) ≤ K) (hQb : (∫ x, ‖Q x‖) ≤ K) :
      ‖planeProduct F P Q E‖ ≤ M*e T*K^2 := by
    apply (planeProduct_bound hF hFc hP hQ hEc hPi hQi hM he0 hFb hEb).trans
    rw [pow_two]
    gcongr
  have H₁ : ‖planeProduct (Ψ T) E G G‖ ≤ M*e T*K^2 := by
    rw [planeProduct_swap01]
    rw [planeProduct_swap12 (hc.comp swap01.continuous) (hcc.comp_homeomorph swap01) hGc hEc hGc]
    exact bnd ((hc.comp swap01.continuous).comp swap12.continuous)
      ((hcc.comp_homeomorph swap01).comp_homeomorph swap12) (fun _ => hb _) hGc hGc hGi hGi hGl hGl
  have H₂ : ‖planeProduct (Ψ T) k E G‖ ≤ M*e T*K^2 := by
    rw [planeProduct_swap12 hc hcc hk.continuous hEc hGc]
    exact bnd (hc.comp swap12.continuous) (hcc.comp_homeomorph swap12) (fun _ => hb _)
      hk.continuous hGc hki hGi hkl hGl
  have H₃ := bnd hc hcc hb hk.continuous hk.continuous hki hki hkl hkl
  change ‖planeProduct (Ψ T) G G G-planeProduct (Ψ T) k k k‖ ≤ _
  rw [planeProduct_telescoping hc hcc hGc hk.continuous]
  linarith only [norm_add_le (planeProduct (Ψ T) E G G + planeProduct (Ψ T) k E G)
      (planeProduct (Ψ T) k k E),
    norm_add_le (planeProduct (Ψ T) E G G) (planeProduct (Ψ T) k E G), H₁, H₂, H₃,
    show 3*M*K^2*e T = 3*(M*e T*K^2) by ring]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.normalizedGamma_L1
#print axioms XiPrime8845.RHTriple.normalizedGamma_plane_replace
