/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairPrimeMain

/-! Connect the density limit of signed pulses back to the two
actual prime factors in the mixed-height ζ explicit formula. -/

noncomputable section
open Complex MeasureTheory Filter Topology Finset

namespace XiPrime8845.RHTriple

theorem primeFactor_dilate_eq_pairPulse (k : ℝ → ℂ) (d b : ℝ)
    {T : ℝ} (hT : 0 < T) :
    primeFactor (dilate k T) (d*Real.log T) b =
      -(T:ℂ)*pairPulse k ⌊T^d⌋₊ T (T*b) true := by
  have hN : ⌊Real.exp (d*Real.log T)⌋₊ = ⌊T^d⌋₊ := by rw [Real.rpow_def_of_pos hT,mul_comm]
  let f (n : ℕ) : ℂ := (_root_.RHTriple.PrimeArithmetic.primeWeight n : ℂ) *
    (dilate k T (Real.log n-b)+dilate k T (-Real.log n-b))
  have hsum : (∑ n ∈ Ioc 0 ⌊T^d⌋₊, f n) = ∑ n ∈ Icc 2 ⌊T^d⌋₊, f n := by
    symm
    apply sum_subset
    · intro n hn
      simp only [mem_Icc, mem_Ioc] at hn ⊢
      omega
    · intro n hn hnn
      have H := mem_Ioc.mp hn
      have he : n = 1 := by simp only [mem_Icc] at hnn; omega
      simp [f,he,_root_.RHTriple.PrimeArithmetic.primeWeight]
  unfold primeFactor
  rw [hN]
  change -(∑ n ∈ Ioc 0 ⌊T^d⌋₊, f n) = _
  rw [hsum]
  unfold pairPulse pairPulseIndex
  rw [product_eq_sprod, sum_product univ (Icc 2 ⌊T^d⌋₊)]
  simp only [Fintype.sum_bool, if_true, signedLog,
    Bool.false_eq_true, if_false, ← sum_add_distrib]
  rw [← sum_neg_distrib, mul_sum]
  apply sum_congr rfl
  intro n _
  unfold f dilate
  rw [mul_sub, mul_sub]
  ring

theorem pairPulse_neg_flip (k : ℝ → ℂ) (N : ℕ) (T x : ℝ) :
    pairPulse k N T (-x) true = pairPulse k N T x false := by
  unfold pairPulse pairPulseIndex
  simp only [product_eq_sprod, sum_product]
  simp only [Fintype.sum_bool, if_true, signedLog,
    Bool.false_eq_true, if_false]
  rw [add_comm]
  congr 1
  · apply sum_congr rfl
    intro n _
    congr 2
    ring
  · apply sum_congr rfl
    intro n _
    congr 2
    ring

def pairPrimeTerm (a b Q : ℝ → ℂ) (d T : ℝ) : ℂ :=
  ∫ t : ℝ, Q t * (primeFactor (dilate a T) (d*Real.log T) (Real.log T*t) *
    primeFactor (dilate b T) (d*Real.log T) (-(Real.log T*t)))

theorem pairPrimeTerm_rescaled (a b Q : ℝ → ℂ) (d : ℝ) {T : ℝ} (hT : 1 < T) :
    pairPrimeTerm a b Q d T / ((T*Real.log T : ℝ):ℂ) = pairPrimeScaled a b Q d T := by
  let W := T*Real.log T
  have ht : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hw : 0 < W := by unfold W; positivity
  have hwc : (W:ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have htc : (T:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hLc : (Real.log T:ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  let F (x : ℝ) := Q (x/W)*
    (pairPulse a ⌊T^d⌋₊ T x true * pairPulse b ⌊T^d⌋₊ T x false)
  have hf (t : ℝ) :
      Q t*(primeFactor (dilate a T) (d*Real.log T) (Real.log T*t) *
        primeFactor (dilate b T) (d*Real.log T) (-(Real.log T*t))) = (T:ℂ)^2*F (W*t) := by
    rw [primeFactor_dilate_eq_pairPulse _ _ _ ht, primeFactor_dilate_eq_pairPulse _ _ _ ht]
    simp only [mul_neg, ← mul_assoc T, pairPulse_neg_flip]
    unfold F
    rw [mul_div_cancel_left₀ _ hw.ne']
    change Q t*((-(T:ℂ)*pairPulse a ⌊T^d⌋₊ T (W*t) true)*
      (-(T:ℂ)*pairPulse b ⌊T^d⌋₊ T (W*t) false)) = _
    ring
  unfold pairPrimeTerm pairPrimeScaled
  simp_rw [hf, integral_const_mul]
  change (T:ℂ)^2*(∫ t, F (W*t))/(W:ℂ) = (∫ x, F x)/(Real.log T:ℂ)^2
  rw [Measure.integral_comp_mul_left F W, abs_of_pos (inv_pos.mpr hw), Complex.real_smul, ofReal_inv]
  unfold W
  push_cast
  field_simp

theorem pairPrime_normalized_tendsto {a b Q : ℝ → ℂ}
    (ha : Continuous a) (hca : HasCompactSupport a)
    (hb : Continuous b) (hcb : HasCompactSupport b)
    (hQ : ContDiff ℝ 1 Q) (hcQ : HasCompactSupport Q) {d : ℝ} (hd : 0 < d) (hd1 : d < 1)
    (hs : ∀ u, d ≤ |u| → Q u = 0) :
    Tendsto (fun T => pairPrimeTerm a b Q d T / ((T*Real.log T : ℝ):ℂ)) atTop
      (𝓝 ((∫ u : ℝ, Q u*((|u|:ℝ):ℂ))*pairHeightMass a b)) := by
  refine (pairPrimeScaled_normalized_tendsto ha hca hb hcb hQ hcQ hd hd1 hs).congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  exact (pairPrimeTerm_rescaled _ _ _ _ hT).symm

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pairPrime_normalized_tendsto
