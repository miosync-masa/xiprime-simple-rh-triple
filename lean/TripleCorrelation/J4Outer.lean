/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.J4Slice

/-! # Region decomposition for `j4`, part 2: the triangle of shifts

`J4R_eq : J4R Pt = ∫ z in Tri, H4 Pt z`, where `Tri = {0 ≤ d ≤ 2, −d ≤ c ≤ 0}` and
`H4 Pt (c, d) = ∫_{hexD ∩ (hexD + (c,d))} P̃(w)·P̃(w − (c,d))·d`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region
open IntCheck IntCheck.Sem

/-! ## generic tools -/

theorem setIntegral_between_int {f : ℝ × ℝ → ℝ} {L U : ℝ → ℝ} (hL : Measurable L)
    (hU : Measurable U) {c e : ℝ} (hce : c ≤ e) (hLU : ∀ y ∈ Icc c e, L y ≤ U y)
    (hint : IntegrableOn f {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)}) :
    ∫ z in {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)}, f z
      = ∫ y in c..e, ∫ x in L y..U y, f (x, y) := by
  set S : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)} with hS
  have mS : MeasurableSet S := by
    have : S = (Prod.snd ⁻¹' Icc c e) ∩ ({z : ℝ × ℝ | L z.2 ≤ z.1} ∩ {z : ℝ × ℝ | z.1 ≤ U z.2}) := by
      ext z; simp [hS, mem_Icc]
    rw [this]
    exact (measurableSet_Icc.preimage measurable_snd).inter
      ((measurableSet_le (hL.comp measurable_snd) measurable_fst).inter
        (measurableSet_le measurable_fst (hU.comp measurable_snd)))
  have hint' : Integrable (S.indicator f) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff mS).2 hint
  have inner : ∀ y, ∫ x, S.indicator f (x, y)
      = (Icc c e).indicator (fun y => ∫ x in L y..U y, f (x, y)) y := by
    intro y
    by_cases hy : y ∈ Icc c e
    · rw [indicator_of_mem hy, ← integral_indicator_Icc _ _ _ (hLU y hy)]
      congr 1; funext x
      have : (x, y) ∈ S ↔ x ∈ Icc (L y) (U y) := ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
      rw [indicator_apply, indicator_apply]
      simp only [this]
    · rw [indicator_of_notMem hy]
      have : ∀ x, S.indicator f (x, y) = 0 := fun x => indicator_of_notMem (fun h => hy h.1) _
      simp [this]
  rw [← integral_indicator mS, Measure.volume_eq_prod, integral_prod_symm _ hint']
  simp only [inner]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hce]

theorem setIntegral_between_int' {f : ℝ × ℝ → ℝ} {L U : ℝ → ℝ} (hL : Measurable L)
    (hU : Measurable U) {c e : ℝ} (hce : c ≤ e) (hLU : ∀ x ∈ Icc c e, L x ≤ U x)
    (hint : IntegrableOn f {z : ℝ × ℝ | z.1 ∈ Icc c e ∧ z.2 ∈ Icc (L z.1) (U z.1)}) :
    ∫ z in {z : ℝ × ℝ | z.1 ∈ Icc c e ∧ z.2 ∈ Icc (L z.1) (U z.1)}, f z
      = ∫ x in c..e, ∫ y in L x..U x, f (x, y) := by
  set S : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.1 ∈ Icc c e ∧ z.2 ∈ Icc (L z.1) (U z.1)} with hS
  have mS : MeasurableSet S := by
    have : S = (Prod.fst ⁻¹' Icc c e) ∩ ({z : ℝ × ℝ | L z.1 ≤ z.2} ∩ {z : ℝ × ℝ | z.2 ≤ U z.1}) := by
      ext z; simp [hS, mem_Icc]
    rw [this]
    exact (measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_le (hL.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hU.comp measurable_fst)))
  have hint' : Integrable (S.indicator f) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff mS).2 hint
  have inner : ∀ x, ∫ y, S.indicator f (x, y)
      = (Icc c e).indicator (fun x => ∫ y in L x..U x, f (x, y)) x := by
    intro x
    by_cases hx : x ∈ Icc c e
    · rw [indicator_of_mem hx, ← integral_indicator_Icc _ _ _ (hLU x hx)]
      congr 1; funext y
      have : (x, y) ∈ S ↔ y ∈ Icc (L x) (U x) := ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [indicator_apply, indicator_apply]
      simp only [this]
    · rw [indicator_of_notMem hx]
      have : ∀ y, S.indicator f (x, y) = 0 := fun y => indicator_of_notMem (fun h => hx h.1) _
      simp [this]
  rw [← integral_indicator mS, Measure.volume_eq_prod, integral_prod _ hint']
  simp only [inner]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hce]

theorem null_graph {g : ℝ → ℝ} (hg : Measurable g) :
    (volume : Measure (ℝ × ℝ)) {z : ℝ × ℝ | z.2 = g z.1} = 0 := by
  have ms : MeasurableSet {z : ℝ × ℝ | z.2 = g z.1} :=
    measurableSet_eq_fun measurable_snd (hg.comp measurable_fst)
  rw [Measure.volume_eq_prod, Measure.measure_prod_null ms]
  refine Filter.Eventually.of_forall fun x => ?_
  have : Prod.mk x ⁻¹' {z : ℝ × ℝ | z.2 = g z.1} = {g x} := by ext y; simp
  simp [this]

theorem null_vert (a : ℝ) : (volume : Measure (ℝ × ℝ)) {z : ℝ × ℝ | z.1 = a} = 0 := by
  have : {z : ℝ × ℝ | z.1 = a} = ({a} : Set ℝ) ×ˢ (univ : Set ℝ) := by ext z; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

/-! ## the function of the shift -/

def W4 (Pt : List (List Int)) (c d : ℝ) (w : ℝ × ℝ) : ℝ :=
  PR Pt w.1 w.2 * PR Pt (w.1 - c) (w.2 - d) * d

theorem W4_continuous (Pt : List (List Int)) (c d : ℝ) : Continuous (W4 Pt c d) := by
  have h1 := PR_continuous Pt
  have h2 : Continuous fun w : ℝ × ℝ => PR Pt (w.1 - c) (w.2 - d) :=
    h1.comp (by fun_prop : Continuous fun w : ℝ × ℝ => (w.1 - c, w.2 - d))
  exact (h1.mul h2).mul continuous_const

noncomputable def H4 (Pt : List (List Int)) (z : ℝ × ℝ) : ℝ :=
  ∫ w in shift2 z.1 z.2, W4 Pt z.1 z.2 w

def Tri : Set (ℝ × ℝ) := {z | (0 ≤ z.2 ∧ z.2 ≤ 2) ∧ (-z.2 ≤ z.1 ∧ z.1 ≤ 0)}

theorem isClosed_hexD : IsClosed hexD := by
  have : hexD = {z : ℝ × ℝ | |z.1| ≤ 1} ∩ ({z : ℝ × ℝ | |z.2| ≤ 1} ∩ {z : ℝ × ℝ | |z.1 + z.2| ≤ 1}) := by
    ext z; simp [hexD]
  rw [this]
  exact (isClosed_le (by fun_prop) continuous_const).inter
    ((isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const))

theorem isClosed_Tri : IsClosed Tri := by
  have : Tri = ({z : ℝ × ℝ | 0 ≤ z.2} ∩ {z : ℝ × ℝ | z.2 ≤ 2})
      ∩ ({z : ℝ × ℝ | -z.2 ≤ z.1} ∩ {z : ℝ × ℝ | z.1 ≤ 0}) := by
    ext z; simp [Tri]
  rw [this]
  exact ((isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const)).inter
    ((isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) continuous_const))

theorem integrableOn_H4 (Pt : List (List Int)) : IntegrableOn (H4 Pt) Tri := by
  let Q : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (Prod.fst ⁻¹' Tri) ∩ ((Prod.snd ⁻¹' hexD)
    ∩ ((fun p : (ℝ × ℝ) × (ℝ × ℝ) => (p.2.1 - p.1.1, p.2.2 - p.1.2)) ⁻¹' hexD))
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => W4 Pt p.1.1 p.1.2 p.2
  have hG : Continuous G := by
    have h1 : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => PR Pt p.2.1 p.2.2 :=
      (PR_continuous Pt).comp continuous_snd
    have h2 : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => PR Pt (p.2.1 - p.1.1) (p.2.2 - p.1.2) :=
      (PR_continuous Pt).comp
        (by fun_prop : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => (p.2.1 - p.1.1, p.2.2 - p.1.2))
    exact (h1.mul h2).mul (by fun_prop)
  have cQ : IsClosed Q := (isClosed_Tri.preimage continuous_fst).inter
    ((isClosed_hexD.preimage continuous_snd).inter (isClosed_hexD.preimage (by fun_prop)))
  have hK : IsCompact ((Icc (-2 : ℝ) 0 ×ˢ Icc (0 : ℝ) 2) ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  have hQK : Q ⊆ (Icc (-2 : ℝ) 0 ×ˢ Icc (0 : ℝ) 2) ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := by
    rintro p ⟨hT, hH, -⟩
    have hT' : (0 ≤ p.1.2 ∧ p.1.2 ≤ 2) ∧ (-p.1.2 ≤ p.1.1 ∧ p.1.1 ≤ 0) := hT
    have hH' := mem_hexD.1 hH
    exact ⟨⟨⟨by linarith [hT'.2.1, hT'.1.2], hT'.2.2⟩, hT'.1⟩, ⟨hH'.1, hH'.2.1⟩⟩
  have hF : Integrable (Q.indicator G)
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff cQ.measurableSet).2
      ((hG.continuousOn.integrableOn_compact hK).mono_set hQK)
  have key := hF.integral_prod_left
  have e : (fun z : ℝ × ℝ => ∫ w, Q.indicator G (z, w)) = Tri.indicator (H4 Pt) := by
    funext z
    by_cases hz : z ∈ Tri
    · rw [indicator_of_mem hz]
      unfold H4
      have ms : MeasurableSet (shift2 z.1 z.2) :=
        (isClosed_hexD.inter (isClosed_hexD.preimage
          (by fun_prop : Continuous fun w : ℝ × ℝ => (w.1 - z.1, w.2 - z.2)))).measurableSet
      rw [← integral_indicator ms]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      have : (z, w) ∈ Q ↔ w ∈ shift2 z.1 z.2 :=
        ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hz, h.1, h.2⟩⟩
      show Q.indicator G (z, w) = (shift2 z.1 z.2).indicator (W4 Pt z.1 z.2) w
      by_cases hw : w ∈ shift2 z.1 z.2
      · rw [indicator_of_mem (this.2 hw), indicator_of_mem hw]
      · rw [indicator_of_notMem (fun h => hw (this.1 h)), indicator_of_notMem hw]
    · rw [indicator_of_notMem hz]
      have : ∀ w, Q.indicator G (z, w) = 0 := fun w => indicator_of_notMem (fun h => hz h.1) _
      simp [this]
  rw [e] at key
  exact (integrable_indicator_iff isClosed_Tri.measurableSet).1 key

end XiPrime8845.Triple.Region

#print axioms XiPrime8845.Triple.Region.integrableOn_H4
