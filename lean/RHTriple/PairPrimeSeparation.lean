/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedSupport
import RHTriple.PrimePairWeight

/-! Distinct signed prime-power pulses are disjoint on the two-point
line strictly below the critical length. The index 1 has weight zero
and is omitted. No analytic prime correlation bound is used here. -/

noncomputable section
open Finset Filter

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

def pairPulseIndex (N : ℕ) : Finset (Bool × ℕ) := univ.product (Icc 2 N)

def pairPulse (k : ℝ → ℂ) (N : ℕ) (T x : ℝ) (reflected : Bool) : ℂ :=
  ∑ i ∈ pairPulseIndex N, (primeWeight i.2 : ℂ) *
    k (if reflected then T*signedLog i.1 i.2-x else x-T*signedLog i.1 i.2)

private theorem signedLog_same_gap {i j : Bool × ℕ} (hi : 2 ≤ i.2) (hj : 2 ≤ j.2)
    (h : i.1 ≠ j.1) :
    1 ≤ |signedLog i.1 i.2-signedLog j.1 j.2| := by
  have h₁ := log_two_le_log hi
  have h₂ := log_two_le_log hj
  rcases i with ⟨is,n⟩
  rcases j with ⟨js,m⟩
  cases is <;> cases js
  · exact (h rfl).elim
  · simp only [signedLog, Bool.false_eq_true, if_false, if_true]
    linarith only [h₁,h₂,neg_abs_le (-Real.log (n:ℝ)-Real.log (m:ℝ))]
  · simp only [signedLog, Bool.false_eq_true, if_false, if_true]
    linarith only [h₁,h₂,le_abs_self (Real.log (n:ℝ)- -Real.log (m:ℝ))]
  · exact (h rfl).elim

theorem pairPulse_centers_separated {d : ℝ} (hd : d < 1) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop, ∀ i ∈ pairPulseIndex ⌊T^d⌋₊, ∀ j ∈ pairPulseIndex ⌊T^d⌋₊, i ≠ j →
      B < |T*signedLog i.1 i.2-T*signedLog j.1 j.2| := by
  have hP : Tendsto (fun T : ℝ => T^(1-d)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [hP.eventually_gt_atTop (2*B), eventually_gt_atTop (max 1 B)]
    with T hpow hT
  have ht : 0 < T := by linarith [le_max_left (1:ℝ) B]
  intro i hi j hj hne
  obtain ⟨hi₁,hi₂⟩ := mem_Icc.mp (mem_product.mp hi).2
  obtain ⟨hj₁,hj₂⟩ := mem_Icc.mp (mem_product.mp hj).2
  have dif (u v : ℝ) : |T*u-T*v| = T*|u-v| := by
    rw [← mul_sub, abs_mul, abs_of_pos ht]
  rw [dif]
  by_cases he : i.1 = j.1
  · have hdiff : i.2 ≠ j.2 := fun h => hne (Prod.ext he h)
    have hh : |signedLog i.1 i.2-signedLog j.1 j.2| =
        |Real.log (i.2:ℝ)-Real.log (j.2:ℝ)| := by
      rw [← he]
      cases i.1
      · simp only [signedLog, Bool.false_eq_true, if_false]
        rw [show -Real.log (i.2:ℝ)- -Real.log (j.2:ℝ) =
          -(Real.log (i.2:ℝ)-Real.log (j.2:ℝ)) by ring, abs_neg]
      · simp [signedLog]
    rw [hh]
    by_contra hnear
    have hi' : (i.2:ℝ) ≤ T^d := (Nat.le_floor_iff (Real.rpow_nonneg ht.le _)).mp hi₂
    have hj' : (j.2:ℝ) ≤ T^d := (Nat.le_floor_iff (Real.rpow_nonneg ht.le _)).mp hj₂
    have hs : Real.sqrt ((i.2:ℝ)*j.2) ≤ T^d := by
      rw [← Real.sqrt_sq (Real.rpow_nonneg ht.le d)]
      exact Real.sqrt_le_sqrt (by rw [pow_two]; gcongr)
    have hmul : T^(1-d)*T^d = T := by
      rw [← Real.rpow_add ht, sub_add_cancel, Real.rpow_one]
    have hcut : 2*B*T^d < T := by
      exact (mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos ht d)).trans_eq hmul
    have hnear' : |Real.log (i.2:ℝ)-Real.log (j.2:ℝ)| ≤ B/T := by
      rw [le_div_iff₀ ht, mul_comm]
      exact le_of_not_gt hnear
    exact hdiff (eq_of_log_gap (by omega) (by omega) ht hB hs hcut hnear')
  · have H := signedLog_same_gap hi₁ hj₁ he
    exact (lt_of_le_of_lt (le_max_right (1:ℝ) B) hT).trans_le
      (le_mul_of_one_le_right ht.le H)

/-- Exact product, after a fixed cutoff margin separates the signed
centres. The first factor is reflected to implement the opposite
frequency in the second factor of the explicit formula. -/
theorem pairPulse_product_eventually_diagonal {a b : ℝ → ℂ} {d R : ℝ}
    (hd : d < 1) (hR : 0 ≤ R)
    (ha : ∀ x, a x ≠ 0 → |x| ≤ R) (hb : ∀ x, b x ≠ 0 → |x| ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ x, pairPulse a ⌊T^d⌋₊ T x true * pairPulse b ⌊T^d⌋₊ T x false =
      ∑ i ∈ pairPulseIndex ⌊T^d⌋₊, (pairedWeight i.2 : ℂ) *
        (a (T*signedLog i.1 i.2-x)*b (x-T*signedLog i.1 i.2)) := by
  filter_upwards [pairPulse_centers_separated hd (2*R) (by positivity)] with T hT
  intro x
  unfold pairPulse
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum, sum_eq_single i]
  · simp only [if_true, Bool.false_eq_true, if_false]
    rw [← primeWeight_sq_eq_pairedWeight, Complex.ofReal_mul]
    ring
  · intro j hj hji
    have hzero : a (T*signedLog i.1 i.2-x) = 0 ∨ b (x-T*signedLog j.1 j.2) = 0 := by
      by_contra! H
      obtain ⟨ha',hb'⟩ := H
      have H' := (abs_add_le (T*signedLog i.1 i.2-x) (x-T*signedLog j.1 j.2)).trans
        (add_le_add (ha _ ha') (hb _ hb'))
      rw [show T*signedLog i.1 i.2-x+(x-T*signedLog j.1 j.2) =
        T*signedLog i.1 i.2-T*signedLog j.1 j.2 by ring] at H'
      exact (not_le_of_gt (hT i hi j hj hji.symm)) (by linarith only [H'])
    rcases hzero with h | h <;> simp [h]
  · intro h
    exact False.elim (h hi)

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pairPulse_centers_separated
#print axioms XiPrime8845.RHTriple.pairPulse_product_eventually_diagonal
