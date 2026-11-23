/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.FocusedLimit

/-! The analytic height factor of (3.46). In AF's Fourier convention
the triple convolution at zero is 1/(2π) times the integral of h³. -/

noncomputable section
open Complex MeasureTheory Filter

namespace XiPrime8845.RHTriple
open Zeta23

theorem heightTripleMass_eq_height_integral {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    (2*Real.pi:ℂ)*heightTripleMass k = ∫ r : ℝ, (paperFT k r)^3 := by
  let K : ℝ × ℝ → ℂ := fun x => k x.1 * k x.2
  let F (x : ℝ × ℝ) (r : ℝ) := K x * (paperFT k r * phase (r*(x.1+x.2)))
  have hi := hk.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc
  have hK : Integrable K := hi.mul_prod hi
  have hP := EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hk hkc)
  have him : Integrable (fun z : (ℝ × ℝ) × ℝ => F z.1 z.2) (volume.prod volume) := by
    have H := (hK.mul_prod hP).mul_bdd (c := 1)
      ((continuous_phase.comp
        (show Continuous (fun z : (ℝ × ℝ) × ℝ => z.2*(z.1.1+z.1.2)) by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun _ => (norm_phase _).le)
    simpa only [F, mul_assoc, Function.comp_apply] using H
  have hx (x : ℝ × ℝ) : (∫ r, F x r) = K x * ((2*Real.pi:ℂ)*k (-(x.1+x.2))) := by
    have h := integral_inverseProfile hk hkc (-(x.1+x.2))
    rw [← h, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [F, inverseProfile, mul_neg, neg_neg]
  have hr (r : ℝ) : (∫ x, F x r) = (paperFT k r)^3 := by
    let f (u : ℝ) := k u * phase (r*u)
    have hF (x : ℝ × ℝ) : F x r = paperFT k r * (f x.1 * f x.2) := by
      have hphase : phase (r*(x.1+x.2)) = phase (r*x.1)*phase (r*x.2) := by
        unfold phase
        rw [← Complex.exp_add]
        push_cast
        congr 1
        ring
      unfold F K f
      rw [hphase]
      ring
    have hf : (∫ u, f u) = paperFT k r := by
      unfold paperFT
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [f, phase, Complex.ofReal_mul, mul_assoc]
    simp_rw [hF]
    rw [integral_const_mul]
    change paperFT k r * (∫ x : ℝ × ℝ, f x.1*f x.2 ∂(volume.prod volume)) = _
    rw [integral_prod_mul f f, hf]
    ring
  calc
    _ = ∫ x, ∫ r, F x r := by
      unfold heightTripleMass planeProduct
      rw [← integral_const_mul]
      simp_rw [hx]
      apply integral_congr_ae
      filter_upwards [] with x
      unfold K
      ring
    _ = ∫ r, ∫ x, F x r := integral_integral_swap him
    _ = _ := by simp_rw [hr]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.heightTripleMass_eq_height_integral
