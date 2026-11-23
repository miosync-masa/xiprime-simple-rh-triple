/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Mathlib

/-! # The (doubled) hexagon as three parallelograms

`hexD = {|X| ≤ 1, |Y| ≤ 1, |X+Y| ≤ 1}` (this is `|X|+|Y|+|X+Y| ≤ 2`).  With the square
`sqC = [-1,0] × [0,1]` and the rotation `σ (X,Y) = (-(X+Y), X)` of order 3:
`∫_{hexD} W = ∫_{sqC} (W + W∘σ + W∘σ²)` for continuous `W` (`integral_hexD`). -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region

noncomputable section

def hexD : Set (ℝ × ℝ) := {z | |z.1| ≤ 1 ∧ |z.2| ≤ 1 ∧ |z.1 + z.2| ≤ 1}
def sqC : Set (ℝ × ℝ) := Icc (-1) 0 ×ˢ Icc 0 1
def σ (z : ℝ × ℝ) : ℝ × ℝ := (-(z.1 + z.2), z.1)
def σ2 (z : ℝ × ℝ) : ℝ × ℝ := (z.2, -(z.1 + z.2))

theorem σ_σ2 (z : ℝ × ℝ) : σ (σ2 z) = z := by ext <;> simp [σ, σ2]
theorem σ2_σ (z : ℝ × ℝ) : σ2 (σ z) = z := by ext <;> simp [σ, σ2]

def σe : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := σ
  invFun := σ2
  left_inv := σ2_σ
  right_inv := σ_σ2
  measurable_toFun := (by fun_prop : Measurable fun z : ℝ × ℝ => (-(z.1 + z.2), z.1))
  measurable_invFun := (by fun_prop : Measurable fun z : ℝ × ℝ => (z.2, -(z.1 + z.2)))

theorem mp_U : MeasurePreserving (fun z : ℝ × ℝ => (z.1, -(z.1 + z.2)))
    (volume : Measure (ℝ × ℝ)) volume := by
  refine MeasurePreserving.skew_product (g := fun x y : ℝ => -(x + y))
    (MeasurePreserving.id (volume : Measure ℝ)) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).comp
    (measurePreserving_add_left (volume : Measure ℝ) x)).map_eq

theorem mp_σ : MeasurePreserving σ (volume : Measure (ℝ × ℝ)) volume :=
  (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).comp mp_U

theorem mp_σ2 : MeasurePreserving σ2 (volume : Measure (ℝ × ℝ)) volume := by
  have h := mp_σ.comp mp_σ
  have e : σ ∘ σ = σ2 := by funext z; ext <;> simp [σ, σ2]
  rwa [e] at h

theorem emb_σ : MeasurableEmbedding σ := σe.measurableEmbedding
theorem emb_σ2 : MeasurableEmbedding σ2 := σe.symm.measurableEmbedding

/-- off the three lines, the hexagon is the disjoint union of the three parallelograms. -/
theorem mem_hexD_iff {z : ℝ × ℝ} (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hs : z.1 + z.2 ≠ 0) :
    z ∈ hexD ↔ (z ∈ sqC ∨ σ2 z ∈ sqC ∨ σ z ∈ sqC) := by
  simp only [hexD, sqC, σ, σ2, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩
    rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy <;>
      rcases lt_or_gt_of_ne hs with hs | hs <;>
      first
        | (left; constructor <;> constructor <;> linarith)
        | (right; left; constructor <;> constructor <;> linarith)
        | (right; right; constructor <;> constructor <;> linarith)
  · rintro (⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩) <;>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem null_lines : ∀ᵐ z : ℝ × ℝ, z.1 ≠ 0 ∧ z.2 ≠ 0 ∧ z.1 + z.2 ≠ 0 := by
  have h1 : (volume : Measure (ℝ × ℝ)) (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  have h2 : (volume : Measure (ℝ × ℝ)) ((univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  have h3 : (volume : Measure (ℝ × ℝ))
      ((fun z : ℝ × ℝ => (z.1, -(z.1 + z.2))) ⁻¹' ((univ : Set ℝ) ×ˢ ({0} : Set ℝ))) = 0 := by
    rw [mp_U.measure_preimage (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet]
    exact h2
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2,
    measure_eq_zero_iff_ae_notMem.1 h3] with z a b c
  refine ⟨fun h => a (by simp [h]), fun h => b (by simp [h]), fun h => c ?_⟩
  simp only [mem_preimage, mem_prod, mem_univ, mem_singleton_iff, true_and]
  linarith

theorem sub_box {z : ℝ × ℝ} (h : z ∈ sqC ∨ σ2 z ∈ sqC ∨ σ z ∈ sqC) :
    z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
  simp only [sqC, σ, σ2, mem_prod, mem_Icc] at h ⊢
  rcases h with ⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem measurableSet_sqC : MeasurableSet sqC := measurableSet_Icc.prod measurableSet_Icc

theorem integral_hexD {W : ℝ × ℝ → ℝ} (hW : Continuous W) :
    ∫ z in hexD, W z = (∫ z in sqC, W z) + (∫ z in sqC, W (σ z)) + ∫ z in sqC, W (σ2 z) := by
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hint : ∀ s : Set (ℝ × ℝ), s ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 → IntegrableOn W s :=
    fun s hs => (hW.continuousOn.integrableOn_compact hK).mono_set hs
  have mA : MeasurableSet (σ2 ⁻¹' sqC) := emb_σ2.measurable measurableSet_sqC
  have mB : MeasurableSet (σ ⁻¹' sqC) := emb_σ.measurable measurableSet_sqC
  have hset : hexD =ᵐ[volume] (sqC ∪ (σ2 ⁻¹' sqC ∪ σ ⁻¹' sqC) : Set (ℝ × ℝ)) := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [null_lines] with z hz
    rw [mem_hexD_iff hz.1 hz.2.1 hz.2.2]; simp [mem_union, mem_preimage]
  have d1 : AEDisjoint volume sqC (σ2 ⁻¹' sqC ∪ σ ⁻¹' sqC) := by
    refine measure_mono_null ?_ (measure_eq_zero_iff_ae_notMem.2 ?_ :
      volume {z : ℝ × ℝ | ¬(z.1 ≠ 0 ∧ z.2 ≠ 0 ∧ z.1 + z.2 ≠ 0)} = 0)
    · rintro z ⟨h1, h2 | h2⟩ <;>
        simp only [sqC, σ, σ2, mem_prod, mem_Icc, mem_preimage] at h1 h2 <;>
        simp only [mem_ofPred_eq, not_and_or, not_not]
      · exact Or.inr (Or.inl (by linarith [h1.2.1, h2.1.2]))
      · exact Or.inl (by linarith [h1.1.2, h2.2.1])
    · filter_upwards [null_lines] with z hz; simpa using hz
  have d2 : AEDisjoint volume (σ2 ⁻¹' sqC) (σ ⁻¹' sqC) := by
    refine measure_mono_null ?_ (measure_eq_zero_iff_ae_notMem.2 ?_ :
      volume {z : ℝ × ℝ | ¬(z.1 ≠ 0 ∧ z.2 ≠ 0 ∧ z.1 + z.2 ≠ 0)} = 0)
    · rintro z ⟨h1, h2⟩
      simp only [sqC, σ, σ2, mem_prod, mem_Icc, mem_preimage] at h1 h2
      simp only [mem_ofPred_eq, not_and_or, not_not]
      exact Or.inr (Or.inr (by linarith [h1.2.1, h2.1.2]))
    · filter_upwards [null_lines] with z hz; simpa using hz
  rw [setIntegral_congr_set hset,
    setIntegral_union₀ d1 (mA.union mB).nullMeasurableSet
      (hint _ fun z hz => sub_box (Or.inl hz))
      (hint _ fun z hz => sub_box (Or.inr hz)),
    setIntegral_union₀ d2 mB.nullMeasurableSet
      (hint _ fun z hz => sub_box (Or.inr (Or.inl hz)))
      (hint _ fun z hz => sub_box (Or.inr (Or.inr hz)))]
  have e1 : ∫ z in σ2 ⁻¹' sqC, W z = ∫ z in sqC, W (σ z) := by
    rw [← mp_σ2.setIntegral_preimage_emb emb_σ2 (fun w => W (σ w)) sqC]
    simp only [σ_σ2]
  have e2 : ∫ z in σ ⁻¹' sqC, W z = ∫ z in sqC, W (σ2 z) := by
    rw [← mp_σ.setIntegral_preimage_emb emb_σ (fun w => W (σ2 w)) sqC]
    simp only [σ2_σ]
  rw [e1, e2]; ring

end

end XiPrime8845.Triple.Region

#print axioms XiPrime8845.Triple.Region.integral_hexD
