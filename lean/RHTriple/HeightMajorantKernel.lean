/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairHeight
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! A nonnegative probability density whose inverse height profile
is compactly supported and C². This is the kernel for the height majorant. -/

noncomputable section
open Complex MeasureTheory Set
open scoped Convolution

namespace XiPrime8845.RHTriple
open Zeta23

private theorem paperFT_real_of_even {v : ℝ → ℝ} (hv : ∀ x, v (-x) = v x)
    (r : ℝ) :
    paperFT (fun x => (v x : ℂ)) r = ((paperFT (fun x => (v x : ℂ)) r).re : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  rw [paperFT_def, ← integral_conj, ← integral_neg_eq_self _ volume]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_mul, Complex.conj_ofReal, hv, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem contDiff_real_paperFT {f : ℝ → ℂ} (hf : Continuous f)
    (hs : HasCompactSupport f) (n : ℕ∞) :
    ContDiff ℝ n (fun r : ℝ => paperFT f r) := by
  have H : ContDiff ℝ n (FourierTransform.fourier f) := by
    apply Real.contDiff_fourier
    intro k _
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hs.norm.mul_left
  have E : (fun r : ℝ => paperFT f r) =
      fun r => FourierTransform.fourier f (-r / (2 * Real.pi)) :=
    funext (Zeta23.EF.paperFT_ofReal_eq_fourier f)
  rw [E]
  exact H.comp (by fun_prop)

set_option maxHeartbeats 1500000 in
theorem height_probability_kernel_exists :
    ∃ k : ℝ → ℂ, ∃ f : ℝ → ℝ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ Continuous f ∧ Integrable f ∧
      (∀ r : ℝ, paperFT k r = (f r:ℂ)) ∧
      (∀ r, 0 ≤ f r) ∧ (∫ r, f r) = 1 := by
  let b : ContDiffBump (0:ℝ) := ⟨1/2,1,by norm_num,by norm_num⟩
  let v := b.normed (volume : Measure ℝ)
  let p (x : ℝ) := (v x:ℂ)
  have hp : ContDiff ℝ 2 p := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hpc : HasCompactSupport p :=
    (b.hasCompactSupport_normed (μ := (volume : Measure ℝ))).comp_left Complex.ofReal_zero
  let q := heightSquareProfile p
  have hq := heightSquareProfile_contDiff hp hpc
  have hqc := heightSquareProfile_compact hpc
  have hv (x : ℝ) : v (-x) = v x := b.normed_neg x
  let F (r : ℝ) : ℝ := (paperFT p r).re^2
  have he (r : ℝ) : paperFT q r = (F r:ℂ) := by
    rw [paperFT_heightSquareProfile hp hpc, paperFT_real_of_even hv]
    simp only [F,p,ofReal_pow]
  have hF : Continuous F := ((Complex.continuous_re.comp
    (contDiff_real_paperFT hp.continuous hpc 1).continuous).pow 2)
  have iF : Integrable F := by
    have H := Zeta23.EF.integrable_paperFT_ofReal (Zeta23.EF.integrable_fourier_of_contDiff_two hq hqc)
    change Integrable (fun r : ℝ => paperFT q r) at H
    have E (r : ℝ) : (paperFT q r).re = F r := by rw [he,ofReal_re]
    have HI := H.re
    change Integrable (fun r : ℝ => (paperFT q r).re) at HI
    simpa only [E] using HI
  have F0 : F 0 = 1 := by
    have H : paperFT p 0 = 1 := by
      unfold paperFT
      simp only [mul_zero,zero_mul,exp_zero,mul_one,p]
      rw [integral_complex_ofReal,b.integral_normed,ofReal_one]
    simp [F,H]
  let C := ∫ r, F r
  have hC : 0 < C := by
    apply (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) iF).mpr
    have hop : IsOpen (Function.support F) := isOpen_ne_fun hF continuous_const
    exact hop.measure_pos _ ⟨0,by simp [Function.mem_support,F0]⟩
  let k (x : ℝ) := (C:ℂ)⁻¹ * q x
  let f (r : ℝ) := F r / C
  refine ⟨k,f,contDiff_const.mul hq,hqc.mul_left,hF.div_const _,iF.div_const _,?_,
    fun _ => div_nonneg (sq_nonneg _) hC.le,?_⟩
  · intro r
    calc
      paperFT k r = (C:ℂ)⁻¹*paperFT q r := by
        unfold paperFT
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp [k]; ring)
      _ = _ := by rw [he]; push_cast [f]; ring
  · unfold f
    rw [integral_div]
    exact div_self hC.ne'

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.height_probability_kernel_exists
