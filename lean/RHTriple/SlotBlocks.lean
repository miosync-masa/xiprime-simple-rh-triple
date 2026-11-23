/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.SlotExclusion
import RHTriple.ExplicitProduct

/-! Expand each member of a finite root set into labelled copies. When
ordinates distinguish roots (as on the critical line), the full collision
of three distinct copies is the third falling factorial, with height cubed. -/

noncomputable section
open Finset

namespace XiPrime8845.RHTriple

theorem slotCollision_eq_factorialMoment {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (γ h : α → ℝ) (hγ : Function.Injective γ) :
    slotCollision (univ : Finset (Σ a : α, Fin (m a))) (γ ∘ Sigma.fst) (h ∘ Sigma.fst) =
      ∑ a : α, (m a : ℝ)*(m a-1)*(m a-2)*(h a)^3 := by
  classical
  unfold slotCollision distinctSlotSum fullSlots
  simp only [Function.comp_apply, Fintype.sum_sigma]
  have hvalue (a : α) (i : Fin (m a)) (b : α) (j : Fin (m b))
      (c : α) (k : Fin (m c)) :
      (if distinctSlots (⟨a,i⟩ : Σ a, Fin (m a)) ⟨b,j⟩ ⟨c,k⟩ then
        if γ a = γ b ∧ γ b = γ c then h a*h b*h c else 0 else 0) =
      if a = b ∧ b = c then
        if distinctSlots (⟨a,i⟩ : Σ a, Fin (m a)) ⟨b,j⟩ ⟨c,k⟩ then
          h a*h b*h c else 0 else 0 := by
    simp only [hγ.eq_iff]
    split <;> split <;> rfl
  simp only [hvalue]
  apply sum_congr rfl
  intro a _
  have inner (i : Fin (m a)) :
      (∑ b : α, ∑ j : Fin (m b), ∑ c : α, ∑ k : Fin (m c),
        if a = b ∧ b = c then
          if distinctSlots (⟨a,i⟩ : Σ a, Fin (m a)) ⟨b,j⟩ ⟨c,k⟩ then
            h a*h b*h c else 0 else 0) =
      ∑ j : Fin (m a), ∑ k : Fin (m a),
        if distinctSlots i j k then (h a)^3 else 0 := by
    rw [sum_eq_single a]
    · apply sum_congr rfl
      intro j _
      rw [sum_eq_single a]
      · apply sum_congr rfl
        intro k _
        simp [distinctSlots, pow_succ, mul_assoc]
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simp_rw [inner]
  rw [← distinct_slots_over_one_zero (m a)]
  unfold distinctSlotSum fullSlots
  simp only [sum_mul]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  split <;> simp

theorem factorialMoment_le_distinctSlots {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (γ h : α → ℝ) (hγ : Function.Injective γ)
    (g : ℝ × ℝ → ℝ) (d : ℝ) (hh : ∀ a, 0 ≤ h a)
    (hg : ∀ x, 0 ≤ g x) (hg0 : g (0,0) = 1) :
    (∑ a : α, (m a : ℝ)*(m a-1)*(m a-2)*(h a)^3) ≤
      distinctSlotSum (univ : Finset (Σ a : α, Fin (m a)))
        (slotTest (γ ∘ Sigma.fst) (h ∘ Sigma.fst) g d) := by
  classical
  rw [← slotCollision_eq_factorialMoment m γ h hγ]
  exact slotCollision_le_distinctSlotSum _ _ _ g d (fun i => hh i.1) hg hg0

open Zeta23 in
/-- Finite ζ zero blocks use actual multiplicities. RH makes the ordinate
injective on distinct roots; it does not identify their different copies. -/
theorem zeta_factorialMoment_le_distinctSlots (hRH : RiemannHypothesis)
    (S : Finset ZetaZero) (h : ℝ → ℝ) (g : ℝ × ℝ → ℝ) (d : ℝ)
    (hh : ∀ t, 0 ≤ h t) (hg : ∀ x, 0 ≤ g x) (hg0 : g (0,0) = 1) :
    let m : S → ℕ := fun a => zetaZeroConfig.mult a.val
    let γ : S → ℝ := fun a => (a.val : ℂ).im
    (∑ a : S, (m a : ℝ)*(m a-1)*(m a-2)*(h (γ a))^3) ≤
      distinctSlotSum (univ : Finset (Σ a : S, Fin (m a)))
        (slotTest (γ ∘ Sigma.fst) ((h ∘ γ) ∘ Sigma.fst) g d) := by
  dsimp only
  refine factorialMoment_le_distinctSlots _ _ _ ?_ g d (fun a => hh _) hg hg0
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · exact (RH_implies_on_line hRH a.val.property).trans
      (RH_implies_on_line hRH b.val.property).symm
  · exact hab

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.slotCollision_eq_factorialMoment
#print axioms XiPrime8845.RHTriple.factorialMoment_le_distinctSlots
#print axioms XiPrime8845.RHTriple.zeta_factorialMoment_le_distinctSlots
