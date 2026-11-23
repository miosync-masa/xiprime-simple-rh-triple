/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedAssembly

/-! The exponential budget left by a pole damps each localized prime
factor. This changes the cost of its L¹ norm to a harmonic sum. -/

noncomputable section
open Complex MeasureTheory Finset ArithmeticFunction

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

def dampedBump (k : ℝ → ℂ) (T a b : ℝ) : ℝ :=
  Real.exp (-|b|/2) * ‖dilate k T (a-b)‖

theorem dampedBump_L1 {k : ℝ → ℂ} (hk : Integrable k)
    {R : ℝ} (hs : ∀ x, k x ≠ 0 → |x| ≤ R) {T : ℝ} (hT : 1 ≤ T) (a : ℝ) :
    Integrable (dampedBump k T a) ∧
      (∫ b, dampedBump k T a b) ≤ Real.exp (R/2) * Real.exp (-|a|/2) * ∫ b, ‖k b‖ := by
  have ht : 0 < T := by linarith
  let S := Real.exp (R/2)*Real.exp (-|a|/2)
  let K (b : ℝ) := ‖dilate k T (a-b)‖
  have hK (b : ℝ) : K b = T*‖k ((-T)*b+T*a)‖ := by
    unfold K dilate
    rw [norm_mul, norm_real, Real.norm_of_nonneg ht.le,
      show T*(a-b) = (-T)*b+T*a by ring]
  have hiK : Integrable K := by
    simp_rw [show K = _ from funext hK]
    exact ((hk.norm.comp_add_right (T*a)).comp_mul_left' (neg_ne_zero.mpr ht.ne')).const_mul T
  have hSK : Integrable (fun b => S*K b) := hiK.const_mul S
  have hpt (b : ℝ) : dampedBump k T a b ≤ S*K b := by
    change Real.exp (-|b|/2)*K b ≤ S*K b
    by_cases hb : K b = 0
    · rw [hb, mul_zero, mul_zero]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    unfold S
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hx := hs (T*(a-b)) (fun h => hb (by simp [K,dilate,h]))
    rw [abs_mul, abs_of_pos ht] at hx
    have hd := (le_div_iff₀ ht).2 (by simpa only [mul_comm] using hx)
    have hR : 0 ≤ R := (mul_nonneg ht.le (abs_nonneg (a-b))).trans hx
    have hR' : R/T ≤ R := (div_le_iff₀ ht).2 (by nlinarith only [mul_nonneg hR (sub_nonneg.mpr hT)])
    have hab := abs_add_le (a-b) b
    rw [sub_add_cancel] at hab
    linarith
  have hi : Integrable (dampedBump k T a) := hSK.mono'
    (((show Continuous (fun b : ℝ => Real.exp (-|b|/2)) by fun_prop).aestronglyMeasurable).mul
      hiK.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => by
      rw [Real.norm_of_nonneg (by unfold dampedBump; positivity)]
      exact hpt b)
  refine ⟨hi, (integral_mono hi hSK hpt).trans_eq ?_⟩
  rw [integral_const_mul]
  simp_rw [hK]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun b : ℝ => ‖k (b+T*a)‖),
    smul_eq_mul, integral_add_right_eq_self (fun b : ℝ => ‖k b‖), inv_neg, abs_neg,
    abs_of_pos (inv_pos.mpr ht), ← mul_assoc T, mul_inv_cancel₀ ht.ne', one_mul]

private theorem primeWeight_damped_log {n : ℕ} (hn : 0 < n) (s : Bool) :
    primeWeight n * Real.exp (-|signedLog s n|/2) = vonMangoldt n / (n:ℝ) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [abs_signedLog hn, show -Real.log (n:ℝ)/2 = -(Real.log (n:ℝ)*(1/2)) by ring,
    Real.exp_neg, ← Real.rpow_def_of_pos hn', ← Real.sqrt_eq_rpow, primeWeight]
  calc
    _ = vonMangoldt n / (Real.sqrt (n:ℝ))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hn'.le]

theorem dampedSignedPrimeFactor_L1 {k : ℝ → ℂ} (hk : Integrable k)
    {R : ℝ} (hs : ∀ x, k x ≠ 0 → |x| ≤ R) {T : ℝ} (hT : 1 ≤ T) (N : ℕ) (s : Bool) :
    let P := fun b => Real.exp (-|b|/2)*‖signedPrimeFactor k T N s b‖
    Integrable P ∧ (∫ b, P b) ≤
      (Real.exp (R/2)*∫ b, ‖k b‖) * (Real.log N * (1+Real.log N)) := by
  let P := fun b => Real.exp (-|b|/2)*‖signedPrimeFactor k T N s b‖
  let H := fun n : ℕ => dampedBump k T (signedLog s n)
  have hi (n : ℕ) : Integrable (fun b => primeWeight n * H n b) :=
    (dampedBump_L1 hk hs hT (signedLog s n)).1.const_mul _
  have hsum : Integrable (fun b => ∑ n ∈ Icc 2 N, primeWeight n * H n b) :=
    integrable_finsetSum _ fun n _ => hi n
  have hpt (b : ℝ) : P b ≤ ∑ n ∈ Icc 2 N, primeWeight n * H n b := by
    change Real.exp (-|b|/2) * ‖∑ n ∈ Icc 2 N, primeWeight n • dilate k T (signedLog s n-b)‖ ≤ _
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_nonneg _)).trans_eq ?_
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    rw [norm_smul, Real.norm_of_nonneg (primeWeight_nonneg n)]
    unfold H dampedBump
    ring
  have hm (n : ℕ) : AEStronglyMeasurable (fun b => primeWeight n • dilate k T (signedLog s n-b))
      (volume : Measure ℝ) := by
    have ht : T ≠ 0 := by linarith
    have hi : Integrable (fun b => k ((-T)*b+T*signedLog s n)) :=
      (hk.comp_add_right _).comp_mul_left' (neg_ne_zero.mpr ht)
    simp only [dilate, show ∀ b, T*(signedLog s n-b)=(-T)*b+T*signedLog s n by intro b; ring]
    rw [show (fun b => primeWeight n • ((T:ℂ)*k ((-T)*b+T*signedLog s n))) =
      fun b => ((primeWeight n:ℝ):ℂ)*((T:ℂ)*k ((-T)*b+T*signedLog s n)) by
      funext b
      rw [real_smul]]
    exact aestronglyMeasurable_const.mul (aestronglyMeasurable_const.mul hi.aestronglyMeasurable)
  have hPm : AEStronglyMeasurable P (volume : Measure ℝ) :=
    ((show Continuous (fun b : ℝ => Real.exp (-|b|/2)) by fun_prop).aestronglyMeasurable).mul
      (Finset.aestronglyMeasurable_fun_sum _ (fun n _ => hm n)).norm
  have hPi : Integrable P := hsum.mono' hPm (Filter.Eventually.of_forall fun b => by
    rw [Real.norm_of_nonneg (by unfold P; positivity)]
    exact hpt b)
  refine ⟨hPi, (integral_mono hPi hsum hpt).trans ?_⟩
  rw [integral_finsetSum _ fun n _ => hi n]
  calc
    _ ≤ ∑ n ∈ Icc 2 N, (Real.exp (R/2)*(∫ b, ‖k b‖)) * (vonMangoldt n/(n:ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
      rw [integral_const_mul]
      refine (mul_le_mul_of_nonneg_left (dampedBump_L1 hk hs hT (signedLog s n)).2
        (primeWeight_nonneg n)).trans_eq ?_
      rw [← primeWeight_damped_log hn0 s]
      ring
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hNlog : 0 ≤ Real.log (N:ℝ) := Real.log_natCast_nonneg N
      calc
        _ ≤ ∑ n ∈ Icc 2 N, Real.log N * (n:ℝ)⁻¹ := by
          apply sum_le_sum
          intro n hn
          have hn' := mem_Icc.mp hn
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
              (by exact_mod_cast hn'.2))) (by positivity)
        _ ≤ _ := by
          rw [← mul_sum]
          apply mul_le_mul_of_nonneg_left _ hNlog
          have hs : Icc (2:ℕ) N ⊆ Icc 1 N := by
            intro n hn
            have hh := mem_Icc.mp hn
            exact mem_Icc.mpr ⟨by omega, hh.2⟩
          have he : Ioc (0:ℕ) N = Icc 1 N := by ext n; simp; omega
          exact (sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => by positivity)).trans
            (by simpa [he] using ordered_harmonic_row 0 N :
              (∑ n ∈ Icc 1 N, (n:ℝ)⁻¹) ≤ 1+Real.log N)

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.dampedBump_L1
#print axioms XiPrime8845.RHTriple.dampedSignedPrimeFactor_L1
