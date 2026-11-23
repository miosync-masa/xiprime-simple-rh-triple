/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairIntegrated
import RHTriple.SlotExclusion

/-! Exact three-slot inclusion–exclusion under absolute convergence.
The equalities in this file compare labels, not ordinates. -/

noncomputable section

namespace XiPrime8845.RHTriple

private theorem tsum_mask_eq {α β : Type*} {p : β → Prop} [DecidablePred p]
    (F : β → ℂ) (e : α → β) (he : Function.Injective e)
    (hr : ∀ x, p x ↔ x ∈ Set.range e) :
    (∑' x, if p x then F x else 0) = ∑' y, F (e y) := by
  have hs : Function.support (fun x => if p x then F x else 0) ⊆ Set.range e := by
    intro x hx
    apply (hr x).1
    by_contra h
    exact hx (if_neg h)
  rw [← he.tsum_eq hs]
  apply tsum_congr
  intro y
  exact if_pos ((hr _).2 ⟨y,rfl⟩)

private theorem mask_summable {α : Type*} (F : α → ℂ) (hF : Summable (fun x => ‖F x‖))
    (p : α → Prop) [DecidablePred p] :
    Summable (fun x => if p x then F x else 0) := by
  refine hF.of_norm_bounded fun x => ?_
  split <;> simp

private theorem indicator_sieve {ι : Type*} [DecidableEq ι] (i j k : ι) (v : ℂ) :
    (if distinctSlots i j k then v else 0) =
      v - (if i = j then v else 0) - (if i = k then v else 0) -
        (if j = k then v else 0) + 2*(if i = j ∧ j = k then v else 0) := by
  by_cases h₁ : i = j
  · subst j
    by_cases h₂ : i = k <;> simp [distinctSlots,h₂] <;> ring
  · by_cases h₂ : i = k
    · subst k
      simp [distinctSlots,h₁,Ne.symm h₁]
    · by_cases h₃ : j = k <;> simp [distinctSlots,h₁,h₂,h₃]

theorem distinctSlotTsum_eq {ι : Type*} [DecidableEq ι]
    (F : (ι × ι) × ι → ℂ) (hF : Summable (fun x => ‖F x‖)) :
    (∑' r, if distinctSlots r.1.1 r.1.2 r.2 then F r else 0) =
      (∑' r, F r) - (∑' p : ι × ι, F ((p.1,p.1),p.2)) -
      (∑' p : ι × ι, F ((p.1,p.2),p.1)) - (∑' p : ι × ι, F ((p.1,p.2),p.2)) +
        2*(∑' i : ι, F ((i,i),i)) := by
  let A (r : (ι×ι)×ι) := if r.1.1 = r.1.2 then F r else 0
  let B (r : (ι×ι)×ι) := if r.1.1 = r.2 then F r else 0
  let C (r : (ι×ι)×ι) := if r.1.2 = r.2 then F r else 0
  let D (r : (ι×ι)×ι) := if r.1.1 = r.1.2 ∧ r.1.2 = r.2 then F r else 0
  have hA : Summable A := mask_summable F hF _
  have hB : Summable B := mask_summable F hF _
  have hC : Summable C := mask_summable F hF _
  have hD : Summable D := mask_summable F hF _
  have hs : Summable F := hF.of_norm
  have h₁ : (∑' r, A r) = ∑' p : ι × ι, F ((p.1,p.1),p.2) := by
    apply tsum_mask_eq F (fun p : ι×ι => ((p.1,p.1),p.2))
    · intro p q h
      exact Prod.ext (congrArg (fun r => r.1.1) h)
        (congrArg (fun r : (ι×ι)×ι => r.2) h)
    · rintro ⟨⟨i,j⟩,k⟩
      constructor
      · intro h
        change i = j at h
        subst j
        exact ⟨(i,k),rfl⟩
      · rintro ⟨⟨a,b⟩,h⟩
        cases h
        rfl
  have h₂ : (∑' r, B r) = ∑' p : ι × ι, F ((p.1,p.2),p.1) := by
    apply tsum_mask_eq F (fun p : ι×ι => (p,p.1))
    · intro p q h
      exact congrArg Prod.fst h
    · rintro ⟨⟨i,j⟩,k⟩
      constructor
      · intro h
        change i = k at h
        subst k
        exact ⟨(i,j),rfl⟩
      · rintro ⟨⟨a,b⟩,h⟩
        cases h
        rfl
  have h₃ : (∑' r, C r) = ∑' p : ι × ι, F ((p.1,p.2),p.2) := by
    apply tsum_mask_eq F (fun p : ι×ι => (p,p.2))
    · intro p q h
      exact congrArg Prod.fst h
    · rintro ⟨⟨i,j⟩,k⟩
      constructor
      · intro h
        change j = k at h
        subst k
        exact ⟨(i,j),rfl⟩
      · rintro ⟨⟨a,b⟩,h⟩
        cases h
        rfl
  have h₄ : (∑' r, D r) = ∑' i : ι, F ((i,i),i) := by
    apply tsum_mask_eq F (fun i : ι => ((i,i),i))
    · intro a b h
      exact congrArg Prod.snd h
    · rintro ⟨⟨i,j⟩,k⟩
      constructor
      · rintro ⟨h,h'⟩
        change i = j at h
        change j = k at h'
        subst j
        subst k
        exact ⟨i,rfl⟩
      · rintro ⟨a,h⟩
        cases h
        exact ⟨rfl,rfl⟩
  have hpoint (r : (ι × ι) × ι) :
      (if distinctSlots r.1.1 r.1.2 r.2 then F r else 0) =
        F r-A r-B r-C r+2*D r := indicator_sieve _ _ _ _
  simp_rw [hpoint]
  rw [((hs.sub hA).sub hB |>.sub hC).tsum_add (hD.mul_left 2)]
  rw [((hs.sub hA).sub hB).tsum_sub hC, (hs.sub hA).tsum_sub hB, hs.tsum_sub hA,
    tsum_mul_left,h₁,h₂,h₃,h₄]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.distinctSlotTsum_eq
