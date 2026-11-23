/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Mathlib

/-! Three ordered slots: exclude equal labels, not equal ordinates.
All statements in this module are finite identities/inequalities. -/

open Finset
open scoped BigOperators
noncomputable section

namespace XiPrime8845.RHTriple

section Finite
variable {ι : Type*} [DecidableEq ι]

def distinctSlots (i j k : ι) : Prop := i ≠ j ∧ i ≠ k ∧ j ≠ k

instance (i j k : ι) : Decidable (distinctSlots i j k) := by
  unfold distinctSlots
  infer_instance

def fullSlots (S : Finset ι) (F : ι → ι → ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S, F i j k

def distinctSlotSum (S : Finset ι) (F : ι → ι → ι → ℝ) : ℝ :=
  fullSlots S fun i j k => if distinctSlots i j k then F i j k else 0

private theorem distinct_indicator (i j k : ι) (v : ℝ) :
    (if distinctSlots i j k then v else 0) =
      v - (if i = j then v else 0) - (if i = k then v else 0) -
        (if j = k then v else 0) + 2*(if i = j ∧ j = k then v else 0) := by
  by_cases h₁ : i = j
  · subst j
    by_cases h₂ : i = k <;> simp [distinctSlots, h₂] <;> ring
  · by_cases h₂ : i = k
    · subst k
      simp [distinctSlots, h₁, Ne.symm h₁]
    · by_cases h₃ : j = k <;> simp [distinctSlots, h₁, h₂, h₃]

theorem distinctSlotSum_eq (S : Finset ι) (F : ι → ι → ι → ℝ) :
    distinctSlotSum S F =
      fullSlots S F -
      (∑ i ∈ S, ∑ k ∈ S, F i i k) -
      (∑ i ∈ S, ∑ j ∈ S, F i j i) -
      (∑ i ∈ S, ∑ j ∈ S, F i j j) +
      2*(∑ i ∈ S, F i i i) := by
  have A : fullSlots S (fun i j k => if i = j then F i j k else 0) =
      ∑ i ∈ S, ∑ k ∈ S, F i i k := by
    unfold fullSlots
    apply sum_congr rfl; intro i hi
    rw [sum_comm]
    apply sum_congr rfl; intro k _
    rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · exact fun h => (h hi).elim
  have B : fullSlots S (fun i j k => if i = k then F i j k else 0) =
      ∑ i ∈ S, ∑ j ∈ S, F i j i := by
    unfold fullSlots
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j _
    rw [sum_eq_single i]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · exact fun h => (h hi).elim
  have C : fullSlots S (fun i j k => if j = k then F i j k else 0) =
      ∑ i ∈ S, ∑ j ∈ S, F i j j := by
    unfold fullSlots
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j hj
    rw [sum_eq_single j]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · exact fun h => (h hj).elim
  have D : fullSlots S (fun i j k => if i = j ∧ j = k then F i j k else 0) =
      ∑ i ∈ S, F i i i := by
    unfold fullSlots
    apply sum_congr rfl; intro i hi
    rw [sum_eq_single i]
    · simp only [true_and]
      rw [sum_eq_single i]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · exact fun h => (h hi).elim
    · intro j _ hj; simp [Ne.symm hj]
    · exact fun h => (h hi).elim
  rw [← A, ← B, ← C, ← D]
  unfold distinctSlotSum fullSlots
  simp_rw [distinct_indicator, sum_add_distrib, sum_sub_distrib, ← mul_sum]

def slotTest (γ h : ι → ℝ) (g : ℝ × ℝ → ℝ) (d : ℝ) (i j k : ι) : ℝ :=
  h i * h j * h k * g (d*(γ i-γ k), d*(γ j-γ k))

def slotCollision (S : Finset ι) (γ h : ι → ℝ) : ℝ :=
  distinctSlotSum S fun i j k => if γ i = γ j ∧ γ j = γ k then h i*h j*h k else 0

theorem slotCollision_le_distinctSlotSum (S : Finset ι) (γ h : ι → ℝ)
    (g : ℝ × ℝ → ℝ) (d : ℝ) (hh : ∀ i, 0 ≤ h i)
    (hg : ∀ x, 0 ≤ g x) (hg0 : g (0,0) = 1) :
    slotCollision S γ h ≤ distinctSlotSum S (slotTest γ h g d) := by
  unfold slotCollision distinctSlotSum fullSlots
  apply sum_le_sum; intro i _
  apply sum_le_sum; intro j _
  apply sum_le_sum; intro k _
  by_cases hs : distinctSlots i j k
  · simp only [if_pos hs]
    by_cases he : γ i = γ j ∧ γ j = γ k
    · simp [slotTest, he.1, he.2, hg0]
    · rw [if_neg he]
      exact mul_nonneg (mul_nonneg (mul_nonneg (hh i) (hh j)) (hh k)) (hg _)
  · simp [hs]

theorem distinctSlotSum_eq_pair_restrictions (S : Finset ι) (γ h : ι → ℝ)
    (g : ℝ × ℝ → ℝ) (d : ℝ) :
    distinctSlotSum S (slotTest γ h g d) =
      fullSlots S (slotTest γ h g d) -
      (∑ i ∈ S, ∑ j ∈ S, (h i)^2*h j*g (d*(γ i-γ j), d*(γ i-γ j))) -
      (∑ i ∈ S, ∑ j ∈ S, h i*(h j)^2*g (d*(γ i-γ j),0)) -
      (∑ i ∈ S, ∑ j ∈ S, h i*(h j)^2*g (0,d*(γ i-γ j))) +
      2*(g (0,0)*∑ i ∈ S, (h i)^3) := by
  rw [distinctSlotSum_eq]
  simp only [slotTest, sub_self, mul_zero]
  have h₁ (i j : ι) : h i*h i*h j = h i^2*h j := by ring
  have h₂ (i j : ι) : h j*h i*h j = h i*h j^2 := by ring
  have h₃ (i j : ι) : h i*h j*h j = h i*h j^2 := by ring
  have h₄ (i : ι) : h i*h i*h i*g (0,0) = g (0,0)*h i^3 := by ring
  simp_rw [h₄, h₁, h₂, h₃]
  -- For the second restriction the singleton slot is put first.
  rw [sum_comm (s := S) (t := S) (f := fun i j => h j*h i^2*g (0,d*(γ j-γ i)))]
  rw [← mul_sum]
  abel

end Finite

theorem distinct_slots_over_one_zero (m : ℕ) :
    distinctSlotSum (univ : Finset (Fin m)) (fun _ _ _ => 1) = (m:ℝ)*(m-1)*(m-2) := by
  rw [distinctSlotSum_eq]
  simp [fullSlots]
  ring

#print axioms distinctSlotSum_eq
#print axioms distinctSlotSum_eq_pair_restrictions
#print axioms slotCollision_le_distinctSlotSum
#print axioms distinct_slots_over_one_zero

end XiPrime8845.RHTriple
