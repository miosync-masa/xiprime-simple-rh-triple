/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PrimeArithmetic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Reciprocal-log-spacing sums for the ζ mixed branches. For three
slots with at least one gamma factor, each surviving prime index is
individually bounded by the hexagonal margin. Thus (3.35)–(3.37) can
be specialized to a single box and the pointwise bound Λ(n) ≤ log n. -/

noncomputable section
open ArithmeticFunction Finset Filter
open scoped Asymptotics

namespace RHTriple.PrimeArithmetic

def primeWeight (n : ℕ) : ℝ := vonMangoldt n / Real.sqrt n

theorem primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight n :=
  div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : Icc 1 (N+1) = insert (N+1) (Icc 1 N) := by
      ext j; simp; omega
    rw [hs, sum_insert (by simp)]
    have ha : 0 < Real.sqrt ((N+1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hb : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N+1 : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt; push_cast; linarith
    have hsq : Real.sqrt ((N+1 : ℕ) : ℝ)^2 - Real.sqrt (N : ℝ)^2 = 1 := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      push_cast; ring
    have hstep : (Real.sqrt ((N+1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((N+1 : ℕ) : ℝ) - Real.sqrt N) := by
      rw [← one_div, div_le_iff₀ ha]
      nlinarith [sq_nonneg (Real.sqrt ((N+1 : ℕ) : ℝ) - Real.sqrt N)]
    linarith

private theorem log_gap_ratio {n m : ℕ} (hn : 0 < n) (hnm : n < m) :
    ((m : ℝ) - n) / m ≤ Real.log (m : ℝ) - Real.log (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast (hn.trans hnm)
  have hh := Real.log_le_sub_one_of_pos (div_pos hn' hm')
  rw [Real.log_div hn'.ne' hm'.ne'] at hh
  rw [sub_div, div_self hm'.ne']
  linarith

/-- Keep the gain from each separation, not just the minimum log gap.
The near range costs `2/(m-n)`, and the far range retains the two square roots. -/
theorem inv_weighted_log_gap_le {n m : ℕ} (hn : 0 < n) (hnm : n < m) :
    1 / ((Real.sqrt n * Real.sqrt m) * (Real.log m - Real.log n)) ≤
      2 / ((m : ℝ)-n) + 2 / (Real.sqrt n * Real.sqrt m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast (hn.trans hnm)
  have hd : 0 < (m : ℝ)-n := sub_pos.mpr (by exact_mod_cast hnm)
  have hs : 0 < Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by positivity
  have hg := log_gap_ratio hn hnm
  have hlog : 0 < Real.log m - Real.log n := (div_pos hd hm').trans_le hg
  by_cases hfar : 2 * (n : ℝ) ≤ m
  · have hg' : (1:ℝ)/2 ≤ Real.log m - Real.log n := by
      apply le_trans _ hg
      rw [le_div_iff₀ hm']; linarith
    have H : 1 / ((Real.sqrt n * Real.sqrt m) * (Real.log m - Real.log n)) ≤
        2 / (Real.sqrt n * Real.sqrt m) := by
      rw [div_le_div_iff₀ (mul_pos hs hlog) hs]
      nlinarith only [mul_le_mul_of_nonneg_left hg' hs.le]
    exact H.trans (le_add_of_nonneg_left (by positivity))
  · have hsm : (m : ℝ) ≤ 2 * (Real.sqrt n * Real.sqrt m) := by
      have H : Real.sqrt (m : ℝ) ≤ 2*Real.sqrt (n : ℝ) := by
        calc
          _ ≤ Real.sqrt (4*(n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
          _ = _ := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), show Real.sqrt 4 = 2 by
              rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      have H' := mul_le_mul_of_nonneg_right H (Real.sqrt_nonneg (m:ℝ))
      rw [← sq, Real.sq_sqrt hm'.le] at H'
      nlinarith
    have hg' : ((m : ℝ)-n) ≤ (Real.log m - Real.log n) * (m : ℝ) := (div_le_iff₀ hm').mp hg
    have hh := mul_le_mul_of_nonneg_left hsm hlog.le
    have H : 1 / ((Real.sqrt n * Real.sqrt m) * (Real.log m - Real.log n)) ≤
        2 / ((m : ℝ)-n) := by
      rw [div_le_div_iff₀ (mul_pos hs hlog) hd]
      linarith only [hg', hh]
    exact H.trans (le_add_of_nonneg_right (by positivity))

theorem ordered_harmonic_row (n N : ℕ) :
    (∑ m ∈ Ioc n N, ((m : ℝ)-n)⁻¹) ≤ 1 + Real.log N := by
  calc
    _ = ∑ j ∈ (Ioc n N).image (fun m => m-n), (j:ℝ)⁻¹ := by
      rw [sum_image]
      · apply sum_congr rfl
        intro m hm
        rw [Nat.cast_sub (mem_Ioc.mp hm).1.le]
      · intro a ha b hb he
        change a ∈ Ioc n N at ha
        change b ∈ Ioc n N at hb
        change a - n = b - n at he
        simp only [mem_Ioc] at ha hb
        omega
    _ ≤ ∑ j ∈ Icc 1 N, (j : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨m,hm,rfl⟩ := mem_image.mp hj
        simp only [mem_Ioc, mem_Icc] at hm ⊢
        omega
      · intro j _ _; positivity
    _ ≤ _ := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log N

/-- The ordered ζ two-prime reciprocal-log sum in a box. The loss is
only polylogarithmic at `N`, rather than a worst-case reciprocal gap. -/
theorem ordered_prime_log_gap_sum_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ m ∈ Ioc n N,
      primeWeight n * primeWeight m / (Real.log m - Real.log n)) ≤
      (Real.log N)^2 * ((N:ℝ) * (10 + 2*Real.log N)) := by
  by_cases hN : N = 0
  · simp [hN]
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
  let l := Real.log N
  have hl : 0 ≤ l := Real.log_nonneg hN1
  let f (n : ℕ) := (Real.sqrt (n : ℝ))⁻¹
  have hmain : ∀ n ∈ Icc 1 N, ∀ m ∈ Ioc n N,
      primeWeight n * primeWeight m / (Real.log m - Real.log n) ≤
        l^2 * (2*((m:ℝ)-n)⁻¹ + 2*(f n * f m)) := by
    intro n hn m hm
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    have hnm := (mem_Ioc.mp hm).1
    have hm0 := hn0.trans hnm
    have hln : vonMangoldt n ≤ l := vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast (mem_Icc.mp hn).2))
    have hlm : vonMangoldt m ≤ l := vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hm0) (by exact_mod_cast (mem_Ioc.mp hm).2))
    have hd : 0 < Real.log m - Real.log n :=
      sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hn0) (by exact_mod_cast hnm))
    have hs : 0 ≤ 1 / (Real.sqrt n * Real.sqrt m * (Real.log m - Real.log n)) := by positivity
    calc
      _ = (vonMangoldt n * vonMangoldt m) *
          (1 / (Real.sqrt n * Real.sqrt m * (Real.log m - Real.log n))) := by
        simp [primeWeight, div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ l^2 * (1 / (Real.sqrt n * Real.sqrt m * (Real.log m - Real.log n))) :=
        mul_le_mul_of_nonneg_right (by rw [sq]; exact mul_le_mul hln hlm vonMangoldt_nonneg hl) hs
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg l)
        simpa only [f, div_eq_mul_inv, mul_inv_rev, one_mul, mul_comm ((Real.sqrt (m:ℝ))⁻¹)]
          using inv_weighted_log_gap_le hn0 hnm
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ m ∈ Ioc n N,
        l^2 * (2*((m:ℝ)-n)⁻¹ + 2*(f n * f m)) := sum_le_sum fun n hn => sum_le_sum (hmain n hn)
    _ ≤ l^2 * (∑ n ∈ Icc 1 N, (2*(1+l) + 2 * (f n * (∑ m ∈ Icc 1 N, f m)))) := by
      simp_rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg l)
      apply sum_le_sum
      intro n hn
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
      have hm : ∑ m ∈ Ioc n N, f m ≤ ∑ m ∈ Icc 1 N, f m := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro m hm; simp only [mem_Ioc, mem_Icc] at hm ⊢; omega
        · intro _ _ _; dsimp [f]; positivity
      have hprod := mul_le_mul_of_nonneg_left hm (show 0 ≤ f n by dsimp [f]; positivity)
      linarith only [ordered_harmonic_row n N, hprod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg l)
      rw [sum_add_distrib, sum_const, Nat.card_Icc, show N+1-1=N by omega, nsmul_eq_mul]
      let S := ∑ n ∈ Icc 1 N, f n
      have hs : (∑ n ∈ Icc 1 N, 2*(f n*S)) = 2*(S*S) := calc
        _ = ∑ n ∈ Icc 1 N, (2*S)*f n := sum_congr rfl fun _ _ => by ring
        _ = _ := by rw [← mul_sum]; unfold S; ring
      rw [hs]
      have hh := sum_inv_sqrt_le N
      change (∑ n ∈ Icc 1 N, f n) ≤ 2 * Real.sqrt N at hh
      have hnn : 0 ≤ ∑ n ∈ Icc 1 N, f n := sum_nonneg fun _ _ => by dsimp [f]; positivity
      have hh' := mul_le_mul hh hh hnn (show 0 ≤ 2 * Real.sqrt N by positivity)
      have hsq := Real.sq_sqrt (Nat.cast_nonneg N : 0 ≤ (N:ℝ))
      change _ ≤ (N:ℝ) * (10+2*l)
      nlinarith only [hh', hsq]

theorem log_two_le_log {n : ℕ} (hn : 2 ≤ n) : (1:ℝ)/2 ≤ Real.log n := by
  have h := log_gap_ratio (n := 1) (m := 2) (by omega) (by omega)
  have h' : (1:ℝ)/2 ≤ Real.log 2 := by norm_num at h ⊢; exact h
  exact h'.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))

theorem single_prime_log_sum_le (N : ℕ) :
    (∑ n ∈ Icc 2 N, primeWeight n / Real.log n) ≤ 2*Real.sqrt N := by
  calc
    _ ≤ ∑ n ∈ Icc 2 N, (Real.sqrt (n:ℝ))⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast show 0 < n by have := (mem_Icc.mp hn).1; omega)
      have hl : 0 < Real.log n := lt_of_lt_of_le (by norm_num) (log_two_le_log (mem_Icc.mp hn).1)
      rw [primeWeight, div_le_iff₀ hl, ← div_eq_inv_mul, div_le_div_iff_of_pos_right hs]
      exact vonMangoldt_le_log
    _ ≤ ∑ n ∈ Icc 1 N, (Real.sqrt (n:ℝ))⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn; simp only [mem_Icc] at hn ⊢; omega
      · intro _ _ _; positivity
    _ ≤ _ := sum_inv_sqrt_le N

theorem prime_weight_sum_le (N : ℕ) : (∑ n ∈ Icc 2 N, primeWeight n) ≤
    2 * Real.log N * Real.sqrt N := by
  by_cases hN : N = 0
  · simp [hN]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN)
  calc
    _ ≤ ∑ n ∈ Icc 2 N, Real.log N * (Real.sqrt (n:ℝ))⁻¹ := by
      apply sum_le_sum
      intro n hn
      unfold primeWeight
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine vonMangoldt_le_log.trans (Real.log_le_log ?_ ?_)
      · exact_mod_cast show 0 < n by have := (mem_Icc.mp hn).1; omega
      · exact_mod_cast (mem_Icc.mp hn).2
    _ ≤ ∑ n ∈ Icc 1 N, Real.log N * (Real.sqrt (n:ℝ))⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn; simp only [mem_Icc] at hn ⊢; omega
      · intro _ _ _; positivity
    _ = Real.log N * (∑ n ∈ Icc 1 N, (Real.sqrt (n:ℝ))⁻¹) := by rw [mul_sum]
    _ ≤ Real.log N * (2 * Real.sqrt N) := mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) hlog
    _ = _ := by ring

theorem same_sign_prime_log_sum_le (N : ℕ) :
    (∑ n ∈ Icc 2 N, ∑ m ∈ Icc 2 N,
      primeWeight n * primeWeight m / (Real.log n + Real.log m)) ≤ 4*(N:ℝ)*(Real.log N)^2 := by
  have h (n m : ℕ) (hn : n ∈ Icc 2 N) (hm : m ∈ Icc 2 N) :
      1 ≤ Real.log n + Real.log m := by
    linarith only [log_two_le_log (mem_Icc.mp hn).1, log_two_le_log (mem_Icc.mp hm).1]
  have hbb := prime_weight_sum_le N
  have hh : 0 ≤ ∑ n ∈ Icc 2 N, primeWeight n := sum_nonneg fun _ _ => primeWeight_nonneg _
  have hsq := mul_le_mul hbb hbb hh (hh.trans hbb)
  calc
    _ ≤ ∑ n ∈ Icc 2 N, ∑ m ∈ Icc 2 N, primeWeight n * primeWeight m := by
      apply sum_le_sum; intro n hn
      apply sum_le_sum; intro m hm
      exact div_le_self (mul_nonneg (primeWeight_nonneg n) (primeWeight_nonneg m)) (h n m hn hm)
    _ = (∑ n ∈ Icc 2 N, primeWeight n) * (∑ m ∈ Icc 2 N, primeWeight m) := by
      simp_rw [← mul_sum, ← sum_mul]
    _ ≤ (2 * Real.log N * Real.sqrt N)*(2 * Real.log N * Real.sqrt N) := hsq
    _ = _ := by
      rw [show (2 * Real.log N * Real.sqrt N)*(2 * Real.log N * Real.sqrt N) =
        4*(Real.sqrt (N:ℝ))^2*(Real.log N)^2 by ring, Real.sq_sqrt (Nat.cast_nonneg N)]

end RHTriple.PrimeArithmetic

#print axioms RHTriple.PrimeArithmetic.ordered_prime_log_gap_sum_le
#print axioms RHTriple.PrimeArithmetic.single_prime_log_sum_le
#print axioms RHTriple.PrimeArithmetic.same_sign_prime_log_sum_le
