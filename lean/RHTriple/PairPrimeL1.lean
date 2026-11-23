/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PolarFactor
import RHTriple.MixedArithmetic

/-! An L1 bound for the actual prime factor on the scaled frequency
line. The strict cutoff then controls its products with the poles
or with the gamma tail. -/

noncomputable section
open Complex MeasureTheory Filter Finset

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

theorem primeFactor_line_norm_integrable_bound {k : ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k) {d T : ℝ}
    (hd : 0 < d) (hT : 1 < T) :
    Integrable (fun t => ‖primeFactor (dilate k T) (d*Real.log T) (Real.log T*t)‖) ∧
      (∫ t, ‖primeFactor (dilate k T) (d*Real.log T) (Real.log T*t)‖) ≤
        4*d*(∫ x, ‖k x‖)*T^(d/2) := by
  let L := Real.log T
  let N := ⌊Real.exp (d*L)⌋₊
  let A := ∫ x, ‖k x‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have ht : 0 < T := zero_lt_one.trans hT
  have hl : 0 < L := Real.log_pos hT
  have hi : Integrable k := hk.integrable_of_hasCompactSupport hkc
  let F (a t : ℝ) := ‖dilate k T (a-L*t)‖
  have hF (a : ℝ) : F a = fun t => T*‖k ((-(T*L))*t+T*a)‖ := by
    funext t
    unfold F dilate
    rw [norm_mul,norm_real,Real.norm_of_nonneg ht.le]
    congr 3 <;> ring
  have iF (a : ℝ) : Integrable (F a) := by
    rw [hF]
    exact ((hi.norm.comp_add_right (T*a)).comp_mul_left'
      (neg_ne_zero.mpr (mul_ne_zero ht.ne' hl.ne'))).const_mul T
  have intF (a : ℝ) : (∫ t, F a t) = A/L := by
    rw [hF, integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖k (x+T*a)‖),
      inv_neg, abs_neg, abs_of_pos (inv_pos.mpr (mul_pos ht hl)), smul_eq_mul,
      integral_add_right_eq_self (fun x => ‖k x‖)]
    change T*((T*L)⁻¹*A) = A/L
    field_simp
  let E (n : ℕ) (t : ℝ) := primeWeight n*(F (Real.log n) t+F (-Real.log n) t)
  have iE (n : ℕ) : Integrable (E n) := ((iF _).add (iF _)).const_mul _
  have intE (n : ℕ) : (∫ t, E n t) = primeWeight n*(2*A/L) := by
    unfold E
    rw [integral_const_mul, integral_add (iF _) (iF _), intF,intF]
    ring
  let P (t : ℝ) := primeFactor (dilate k T) (d*L) (L*t)
  have hP : Continuous P := (primeFactor_continuous (by unfold dilate; fun_prop)
    (d*L)).comp (continuous_const.mul continuous_id)
  have hpoint (t : ℝ) : ‖P t‖ ≤ ∑ n ∈ Icc 2 N, E n t := by
    unfold P primeFactor
    rw [norm_neg]
    refine (norm_sum_le _ _).trans ?_
    have hsum : (∑ n ∈ Ioc 0 N, E n t) = ∑ n ∈ Icc 2 N, E n t := by
      symm
      apply sum_subset
      · intro n hn
        simp only [mem_Icc,mem_Ioc] at hn ⊢
        omega
      · intro n hn hnn
        have H := mem_Ioc.mp hn
        have e : n = 1 := by simp only [mem_Icc] at hnn; omega
        simp [e,E,primeWeight]
    rw [← hsum]
    apply sum_le_sum
    intro n _
    simp only [E,F,norm_mul,norm_real]
    change ‖primeWeight n‖ * _ ≤ primeWeight n * _
    rw [Real.norm_of_nonneg (primeWeight_nonneg n)]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (primeWeight_nonneg n)
  have iD : Integrable (fun t => ∑ n ∈ Icc 2 N, E n t) :=
    integrable_finsetSum _ (fun n _ => iE n)
  have iP : Integrable (fun t => ‖P t‖) :=
    iD.mono' hP.norm.aestronglyMeasurable (Eventually.of_forall fun t => by simpa only [norm_norm] using hpoint t)
  refine ⟨iP,(integral_mono iP iD hpoint).trans ?_⟩
  rw [integral_finsetSum _ (fun n _ => iE n)]
  simp_rw [intE]
  rw [← sum_mul]
  have he : (1:ℝ) ≤ Real.exp (d*L) := by rw [Real.one_le_exp_iff]; positivity
  have hn : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos _).le).2 (by exact_mod_cast he)
  have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : (N:ℝ) ≤ Real.exp (d*L) := Nat.floor_le (Real.exp_pos _).le
  have hlog : Real.log N ≤ d*L := (Real.log_le_log hn0 hbound).trans_eq (Real.log_exp _)
  have hroot : Real.sqrt N ≤ T^(d/2) := by
    refine (Real.sqrt_le_sqrt hbound).trans_eq ?_
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos ht]
    congr 1
    unfold L
    ring
  calc
    _ ≤ (2*Real.log N*Real.sqrt N)*(2*A/L) :=
      mul_le_mul_of_nonneg_right (prime_weight_sum_le _) (by positivity)
    _ ≤ (2*(d*L)*T^(d/2))*(2*A/L) := by gcongr
    _ = _ := by field_simp <;> ring

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.primeFactor_line_norm_integrable_bound
