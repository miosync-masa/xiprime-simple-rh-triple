/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedArithmetic
import Zeta23.XiPrime.Coeff.NonSquarefree

/-! The arithmetic limit for one opposite-sign pair. In the normalized
logarithmic coordinate, the weights Λ(n)²/n tend to the density `u du`.
Use AF's elementary Mertens step and the proper-prime-power defect;
the pair-correlation mean-square machinery is not needed. -/

noncomputable section
open Complex MeasureTheory Filter Topology Finset

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic
open Zeta23.XiPrime

def pairedWeight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n ^ 2 / (n:ℝ)

theorem pairedWeight_nonneg (n : ℕ) : 0 ≤ pairedWeight n := by unfold pairedWeight; positivity

theorem primeWeight_sq_eq_pairedWeight (n : ℕ) : primeWeight n * primeWeight n = pairedWeight n := by
  unfold primeWeight pairedWeight
  rw [← pow_two, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem primePairMass_eventually_bounded {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      (∑ n ∈ Ioc 0 ⌊Real.exp (d*L)⌋₊, pairedWeight n)/L^2 ≤ C := by
  obtain ⟨B,hB⟩ := Zeta23.Cheb.chebyshevMertens.cheb2a
  refine ⟨d^2/2+|B| * d, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (Real.log 2/d)] with L hL hL'
  have hl : 0 < L := by linarith
  have hx : 2 ≤ Real.exp (d*L) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_le_exp]
    simpa only [mul_comm] using (div_le_iff₀ hd).1 hL'
  have H := hB (Real.exp (d*L)) hx
  simp only [Real.log_exp] at H
  have HH := (abs_le.mp H).2
  change (∑ n ∈ Ioc 0 ⌊Real.exp (d*L)⌋₊, pairedWeight n) - (d*L)^2/2 ≤ B*(d*L) at HH
  rw [div_le_iff₀ (sq_pos_of_pos hl)]
  have hLL : L ≤ L^2 := by nlinarith only [mul_nonneg hl.le (sub_nonneg.mpr hL)]
  have hp := mul_le_mul_of_nonneg_left hLL (mul_nonneg (abs_nonneg B) hd.le)
  have HB := mul_le_mul_of_nonneg_right (le_abs_self B) (mul_nonneg hd.le hl.le)
  nlinarith only [HH, hp, HB]

private theorem real_profile_bound {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |f x| ≤ K := by
  obtain ⟨B,hB⟩ := hfc.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · rw [← Real.norm_eq_abs]
    exact (hB x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact le_max_right _ _

theorem primePairWeight_real_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {d : ℝ} (hd : 0 < d)
    (hs : ∀ x, d ≤ x → f x = 0) :
    Tendsto (fun L : ℝ =>
      (∑ n ∈ Ioc 0 ⌊Real.exp (d*L)⌋₊, pairedWeight n*f (Real.log n/L))/L^2)
      atTop (𝓝 (∫ u in (0:ℝ)..d, f u*u)) := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by decide)
  obtain ⟨B,hB,hfb⟩ := real_profile_bound hf.continuous hfc
  obtain ⟨J,hJ,hdb⟩ := real_profile_bound hdf hfc.deriv
  let D := KM * ((B+d*J)*d) + B*Cdef
  have hlim : Tendsto (fun L : ℝ => D/L) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).const_mul D)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL1
  have hl : 0 < L := by linarith
  have hY : 0 ≤ d*L := by positivity
  let g (y : ℝ) := y*f (y/L)
  let gp (y : ℝ) := f (y/L)+y*(deriv f (y/L)/L)
  have hg (y : ℝ) : HasDerivAt g (gp y) y := by
    have h := (hasDerivAt_id y).mul ((hf.differentiable (by decide) (y/L)).hasDerivAt.comp y
      ((hasDerivAt_id y).div_const L))
    have eqg : ((id : ℝ → ℝ) * (f ∘ fun x : ℝ => id x/L)) = g := rfl
    rw [eqg] at h
    simpa [gp, div_eq_mul_inv, mul_assoc] using h
  have hgc : Continuous gp := by
    unfold gp
    exact (hf.continuous.comp (continuous_id.div_const L)).add
      (continuous_id.mul ((hdf.comp (continuous_id.div_const L)).div_const L))
  have hb (y : ℝ) (hy : y ∈ Set.Icc 0 (d*L)) : |gp y| ≤ B+d*J := by
    unfold gp
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_div, abs_of_nonneg hy.1, abs_of_pos hl]
    have hy' := (div_le_iff₀ hl).2 hy.2
    exact add_le_add (hfb _) (by
      rw [← mul_div_assoc, ← div_mul_eq_mul_div]
      exact mul_le_mul hy' (hdb _) (abs_nonneg _) hd.le)
  have hr : (∫ y in (0:ℝ)..(d*L), |gp y|) ≤ (B+d*J)*(d*L) := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hY (hgc.abs.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) hb
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm (d*L)] using H
  have hz : g (d*L) = 0 := by unfold g; rw [mul_div_cancel_right₀ _ hl.ne', hs _ le_rfl, mul_zero]
  have E := mertens_step hY (fun y _ => hg y) hgc.continuousOn
  rw [hz,abs_zero,zero_add] at E
  have hint : (∫ y in (0:ℝ)..(d*L), g y) = L^2*∫ u in (0:ℝ)..d, f u*u := by
    have he (y : ℝ) : g y = L * (f (L⁻¹*y)*(L⁻¹*y)) := by
      unfold g
      rw [show y/L=L⁻¹*y by ring]
      field_simp
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u : ℝ => f u*u) (inv_ne_zero hl.ne')]
    simp only [mul_zero, inv_inv, smul_eq_mul]
    rw [show L⁻¹*(d*L)=d by field_simp]
    ring
  let idx := Ioc 0 ⌊Real.exp (d*L)⌋₊
  let S := ∑ n ∈ idx, pairedWeight n*f (Real.log n/L)
  let M := ∑ n ∈ idx, ArithmeticFunction.vonMangoldt n / (n:ℝ) * g (Real.log n)
  let I := ∫ u in (0:ℝ)..d, f u*u
  let w (n : ℕ) := ArithmeticFunction.vonMangoldt n*(Real.log n-ArithmeticFunction.vonMangoldt n)/(n:ℝ)
  have err : |M - S| ≤ B*Cdef := by
    have hsum : M-S = ∑ n ∈ idx, w n*f (Real.log n/L) := by
      unfold M S
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro n _
      unfold w g pairedWeight
      ring
    rw [hsum, ← Real.norm_eq_abs]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ n ∈ idx, B*w n := by
        apply sum_le_sum
        intro n _
        have hn : 0 ≤ w n := defect_term_nonneg n
        rw [norm_mul, Real.norm_of_nonneg hn, Real.norm_eq_abs, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hfb _) hn
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (defect_le (Real.exp (d*L))) hB
  rw [hint] at E
  have bnd : |S-L^2*I| ≤ D*L := by
    have hE : |M-L^2*I| ≤ KM*((B+d*J)*(d*L)) :=
      E.trans (mul_le_mul_of_nonneg_left hr KM_nonneg)
    have hDE : 0 ≤ B*Cdef := mul_nonneg hB (by norm_num [Cdef])
    have h := abs_sub_le S M (L^2*I)
    rw [abs_sub_comm S M] at h
    unfold D
    nlinarith only [h, err, hE, mul_nonneg hDE (sub_nonneg.mpr hL1)]
  change ‖S/L^2-I‖ ≤ D/L
  rw [Real.norm_eq_abs, show S/L^2-I = (S-L^2*I)/L^2 by field_simp,
    abs_div, abs_of_pos (by positivity : 0 < L^2)]
  exact (div_le_div_of_nonneg_right bnd (by positivity)).trans_eq (by field_simp)

theorem primePairWeight_complex_tendsto {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {d : ℝ} (hd : 0 < d)
    (hs : ∀ x, d ≤ x → f x = 0) :
    Tendsto (fun L : ℝ =>
      (∑ n ∈ Ioc 0 ⌊Real.exp (d*L)⌋₊, (pairedWeight n : ℂ)*f (Real.log n/L))/(L:ℂ)^2)
      atTop (𝓝 (∫ u in (0:ℝ)..d, f u*(u:ℂ))) := by
  let fR (x : ℝ) := (f x).re
  let fI (x : ℝ) := (f x).im
  have hR : ContDiff ℝ 1 fR := Complex.reCLM.contDiff.comp hf
  have hI : ContDiff ℝ 1 fI := Complex.imCLM.contDiff.comp hf
  have hRc : HasCompactSupport fR :=
    hfc.comp_left (show Complex.reCLM (0:ℂ) = 0 by simp)
  have hIc : HasCompactSupport fI :=
    hfc.comp_left (show Complex.imCLM (0:ℂ) = 0 by simp)
  have hr := primePairWeight_real_tendsto hR hRc hd (fun x hx => by simp [fR, hs x hx])
  have hi := primePairWeight_real_tendsto hI hIc hd (fun x hx => by simp [fI, hs x hx])
  have hr' := (Complex.continuous_ofReal.tendsto _).comp hr
  have hi' := ((Complex.continuous_ofReal.tendsto _).comp hi).mul_const Complex.I
  have hh := hr'.add hi'
  have hF (x : ℝ) : f x = (fR x : ℂ)+(fI x : ℂ)*Complex.I :=
    (Complex.re_add_im (f x)).symm
  have htarget : (∫ u in (0:ℝ)..d, f u*(u:ℂ)) =
      ((∫ u in (0:ℝ)..d, fR u*u):ℝ) + ((∫ u in (0:ℝ)..d, fI u*u):ℝ)*Complex.I := by
    have hrI : IntervalIntegrable (fun u => (fR u : ℂ)*(u:ℂ)) volume 0 d :=
      ((Complex.continuous_ofReal.comp hR.continuous).mul Complex.continuous_ofReal).intervalIntegrable _ _
    have hiI : IntervalIntegrable (fun u => (fI u : ℂ)*(u:ℂ)) volume 0 d :=
      ((Complex.continuous_ofReal.comp hI.continuous).mul Complex.continuous_ofReal).intervalIntegrable _ _
    rw [show (fun u : ℝ => f u*(u:ℂ)) =
      fun u => (fR u : ℂ)*(u:ℂ)+((fI u : ℂ)*(u:ℂ))*Complex.I by
        funext u; rw [hF]; ring,
      intervalIntegral.integral_add hrI (hiI.mul_const _), intervalIntegral.integral_mul_const]
    simp only [← Complex.ofReal_mul, intervalIntegral.integral_ofReal]
  rw [← htarget] at hh
  refine hh.congr' (Eventually.of_forall fun L => ?_)
  simp only [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sum,
    Complex.ofReal_mul]
  rw [← mul_div_right_comm, ← add_div, sum_mul, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro n _
  rw [hF]
  ring

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.primePairMass_eventually_bounded
#print axioms XiPrime8845.RHTriple.primePairWeight_real_tendsto
#print axioms XiPrime8845.RHTriple.primePairWeight_complex_tendsto
