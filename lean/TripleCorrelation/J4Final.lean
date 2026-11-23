/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.J4Outer

/-! # Region decomposition for `j4`, part 3: `J4R Pt = ∫ z in Tri, H4 Pt z`

`Tri = A1 ∪ A2 ∪ A3 ∪ A4` (overlaps on three lines); on each `A_k` the slice lemma gives the
checker's pieces.  `A1`, `A2` are integrated with `d` outside, `A3`, `A4` with `c` outside,
exactly as in the checker. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region
open IntCheck IntCheck.Sem

def A1 : Set (ℝ × ℝ) := {z | z.2 ∈ Icc (1 : ℝ) 2 ∧ z.1 ∈ Icc (-z.2) (-1)}
def A2 : Set (ℝ × ℝ) := {z | z.2 ∈ Icc (1 : ℝ) 2 ∧ z.1 ∈ Icc (1 - z.2) 0}
def A3 : Set (ℝ × ℝ) := {z | z.1 ∈ Icc (-1 : ℝ) 0 ∧ z.2 ∈ Icc (-2 * z.1) (1 - z.1)}
def A4 : Set (ℝ × ℝ) := {z | z.1 ∈ Icc (-1 : ℝ) 0 ∧ z.2 ∈ Icc (-z.1) (-2 * z.1)}

theorem ms_between (L U : ℝ → ℝ) (hL : Measurable L) (hU : Measurable U) (c e : ℝ) :
    MeasurableSet {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)} := by
  have : {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)}
      = (Prod.snd ⁻¹' Icc c e) ∩ ({z : ℝ × ℝ | L z.2 ≤ z.1} ∩ {z : ℝ × ℝ | z.1 ≤ U z.2}) := by
    ext z; simp [mem_Icc]
  rw [this]
  exact (measurableSet_Icc.preimage measurable_snd).inter
    ((measurableSet_le (hL.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst (hU.comp measurable_snd)))

theorem ms_between' (L U : ℝ → ℝ) (hL : Measurable L) (hU : Measurable U) (c e : ℝ) :
    MeasurableSet {z : ℝ × ℝ | z.1 ∈ Icc c e ∧ z.2 ∈ Icc (L z.1) (U z.1)} := by
  have : {z : ℝ × ℝ | z.1 ∈ Icc c e ∧ z.2 ∈ Icc (L z.1) (U z.1)}
      = (Prod.fst ⁻¹' Icc c e) ∩ ({z : ℝ × ℝ | L z.1 ≤ z.2} ∩ {z : ℝ × ℝ | z.2 ≤ U z.1}) := by
    ext z; simp [mem_Icc]
  rw [this]
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_le (hL.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hU.comp measurable_fst)))

theorem mA2 : MeasurableSet A2 := ms_between (fun y => 1 - y) (fun _ => 0) (by fun_prop) (by fun_prop) 1 2
theorem mA3 : MeasurableSet A3 :=
  ms_between' (fun x => -2 * x) (fun x => 1 - x) (by fun_prop) (by fun_prop) (-1) 0
theorem mA4 : MeasurableSet A4 :=
  ms_between' (fun x => -x) (fun x => -2 * x) (by fun_prop) (by fun_prop) (-1) 0

theorem Tri_eq : Tri = A1 ∪ (A2 ∪ (A3 ∪ A4)) := by
  ext z
  simp only [Tri, A1, A2, A3, A4, mem_ofPred_eq, mem_union, mem_Icc]
  constructor
  · rintro ⟨⟨d0, d2⟩, c1, c0⟩
    by_cases h1 : z.1 ≤ -1
    · exact Or.inl ⟨⟨by linarith, d2⟩, c1, h1⟩
    · by_cases h2 : 1 - z.1 ≤ z.2
      · exact Or.inr (Or.inl ⟨⟨by linarith, d2⟩, by linarith, c0⟩)
      · by_cases h3 : -2 * z.1 ≤ z.2
        · exact Or.inr (Or.inr (Or.inl ⟨⟨by linarith, c0⟩, h3, by linarith⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨⟨by linarith, c0⟩, by linarith, by linarith⟩))
  · rintro (⟨⟨a, b⟩, c, d⟩ | ⟨⟨a, b⟩, c, d⟩ | ⟨⟨a, b⟩, c, d⟩ | ⟨⟨a, b⟩, c, d⟩) <;>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem d1 : AEDisjoint volume A1 (A2 ∪ (A3 ∪ A4)) := by
  refine measure_mono_null ?_ (null_vert (-1))
  rintro z ⟨h1, h2⟩
  simp only [A1, A2, A3, A4, mem_ofPred_eq, mem_union, mem_Icc] at h1 h2 ⊢
  rcases h2 with ⟨⟨a, b⟩, c, d⟩ | ⟨⟨a, b⟩, c, d⟩ | ⟨⟨a, b⟩, c, d⟩ <;> linarith [h1.2.2, h1.1.2]

theorem d2 : AEDisjoint volume A2 (A3 ∪ A4) := by
  refine measure_mono_null ?_ (null_graph (g := fun x => 1 - x) (by fun_prop))
  rintro z ⟨h1, h2⟩
  simp only [A2, A3, A4, mem_ofPred_eq, mem_union, mem_Icc] at h1 h2 ⊢
  rcases h2 with ⟨⟨a, b⟩, c, d⟩ | ⟨⟨a, b⟩, c, d⟩ <;> linarith [h1.2.1]

theorem d3 : AEDisjoint volume A3 A4 := by
  refine measure_mono_null ?_ (null_graph (g := fun x => -2 * x) (by fun_prop))
  rintro z ⟨h1, h2⟩
  simp only [A3, A4, mem_ofPred_eq, mem_Icc] at h1 h2 ⊢
  linarith [h1.2.1, h2.2.2]

theorem outer_congr {a b : ℝ} (hab : a ≤ b) {L U L' U' : ℝ → ℝ} (hL : ∀ y, L' y = L y)
    (hU : ∀ y, U' y = U y) (hLU : ∀ y ∈ Icc a b, L y ≤ U y)
    {F G : ℝ → ℝ → ℝ} (h : ∀ y ∈ Icc a b, ∀ x ∈ Icc (L y) (U y), F y x = G y x) :
    ∫ y in a..b, ∫ x in L' y..U' y, F y x = ∫ y in a..b, ∫ x in L y..U y, G y x := by
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le hab] at hy
  show ∫ x in L' y..U' y, F y x = ∫ x in L y..U y, G y x
  rw [hL y, hU y]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (hLU y hy)] at hx
  exact h y hy x hx

theorem rev3 {a b c a' b' c' : ℝ} (h1 : a = c') (h2 : b = b') (h3 : c = a') :
    a + (b + c) = a' + (b' + c') := by subst h1 h2 h3; ring

theorem cdR_eval (W : ℝ × ℝ × Unit → ℝ) (a1 b1 a2 b2 : Int) (da db : ℝ) :
    cdR W a1 b1 a2 b2 da db
      = ∫ y in da..db, ∫ x in ((b1 : ℝ) + a1 * y)..((b2 : ℝ) + a2 * y), W (x, (y, ())) := by
  simp only [cdR, XYR, lin1_sem]

theorem pc_eval (Pt : List (List Int)) (zc : Bool)
    (cy1 a1 b1 c1 cy2 a2 b2 c2 a3 b3 c3 a4 b4 c4 : Int) (c d : ℝ) :
    pc Pt zc cy1 a1 b1 c1 cy2 a2 b2 c2 a3 b3 c3 a4 b4 c4 (c, (d, ()))
      = ∫ y in ((c3 : ℝ) + b3 * d + a3 * c)..((c4 : ℝ) + b4 * d + a4 * c),
          ∫ x in ((c1 : ℝ) + b1 * d + a1 * c + cy1 * y)..((c2 : ℝ) + b2 * d + a2 * c + cy2 * y),
            (if zc then W4 Pt c d (x, y) else W4 Pt d c (x, y)) := by
  have hF : ∀ (cv a b k : Int) (y : ℝ),
      lv3.f (Gen.F IntCheck.o2 cv (IntCheck.lin2 a b k)) (y, (c, (d, ())))
        = (k : ℝ) + b * d + a * c + cv * y := by
    intro cv a b k y
    have := F_sem lv2 cv (IntCheck.lin2 a b k) y (c, (d, ()))
    rw [lin2_sem] at this
    exact this
  cases zc <;> simp only [pc, XYR, hF, lin2_sem, Q_sem, W4, if_true, if_false, Bool.false_eq_true]

theorem J4R_eq (Pt : List (List Int)) : J4R Pt = ∫ z in Tri, H4 Pt z := by
  have hI := integrableOn_H4 Pt
  have s1 : A1 ⊆ Tri := by rw [Tri_eq]; exact subset_union_left
  have s2 : A2 ⊆ Tri := by rw [Tri_eq]; exact fun z h => Or.inr (Or.inl h)
  have s3 : A3 ⊆ Tri := by rw [Tri_eq]; exact fun z h => Or.inr (Or.inr (Or.inl h))
  have s4 : A4 ⊆ Tri := by rw [Tri_eq]; exact fun z h => Or.inr (Or.inr (Or.inr h))
  have s234 : A2 ∪ (A3 ∪ A4) ⊆ Tri := union_subset s2 (union_subset s3 s4)
  have s34 : A3 ∪ A4 ⊆ Tri := union_subset s3 s4
  have split : ∫ z in Tri, H4 Pt z = (∫ z in A1, H4 Pt z) + ((∫ z in A2, H4 Pt z)
      + ((∫ z in A3, H4 Pt z) + ∫ z in A4, H4 Pt z)) := by
    conv_lhs => rw [Tri_eq]
    rw [setIntegral_union₀ d1 (mA2.union (mA3.union mA4)).nullMeasurableSet (hI.mono_set s1)
        (hI.mono_set s234),
      setIntegral_union₀ d2 (mA3.union mA4).nullMeasurableSet (hI.mono_set s2) (hI.mono_set s34),
      setIntegral_union₀ d3 mA4.nullMeasurableSet (hI.mono_set s3) (hI.mono_set s4)]
  have e1 : ∫ z in A1, H4 Pt z = ∫ y in (1 : ℝ)..2, ∫ x in (-y)..(-1 : ℝ), H4 Pt (x, y) :=
    setIntegral_between_int (L := fun y => -y) (U := fun _ => -1) (by fun_prop) (by fun_prop)
      (by norm_num) (fun y hy => by linarith [hy.1]) (hI.mono_set s1)
  have e2 : ∫ z in A2, H4 Pt z = ∫ y in (1 : ℝ)..2, ∫ x in (1 - y)..(0 : ℝ), H4 Pt (x, y) :=
    setIntegral_between_int (L := fun y => 1 - y) (U := fun _ => 0) (by fun_prop) (by fun_prop)
      (by norm_num) (fun y hy => by linarith [hy.1]) (hI.mono_set s2)
  have e3 : ∫ z in A3, H4 Pt z = ∫ x in (-1 : ℝ)..0, ∫ y in (-2 * x)..(1 - x), H4 Pt (x, y) :=
    setIntegral_between_int' (L := fun x => -2 * x) (U := fun x => 1 - x) (by fun_prop)
      (by fun_prop) (by norm_num) (fun x hx => by linarith [hx.1]) (hI.mono_set s3)
  have e4 : ∫ z in A4, H4 Pt z = ∫ x in (-1 : ℝ)..0, ∫ y in (-x)..(-2 * x), H4 Pt (x, y) :=
    setIntegral_between_int' (L := fun x => -x) (U := fun x => -2 * x) (by fun_prop)
      (by fun_prop) (by norm_num) (fun x hx => by linarith [hx.2]) (hI.mono_set s4)
  have hW := W4_continuous Pt
  rw [split, e1, e2, e3, e4, ← add_assoc, ← add_assoc]
  unfold J4R
  rw [cdR_eval, cdR_eval, cdR_eval, cdR_eval]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · -- A1
    refine outer_congr (by norm_num) (fun y => by push_cast; ring) (fun y => by push_cast; ring)
      (fun y hy => by linarith [hy.1]) fun d hd c hc => ?_
    show _ = H4 Pt (c, d)
    unfold H4
    rw [slice_A1 (hW c d) hd.1 hd.2 hc.1 hc.2, pc_eval]
    exact ii_congr (by push_cast; ring) (by push_cast; ring) fun y =>
      ii_congr (by push_cast; ring) (by push_cast; ring) fun x => rfl
  · -- A2
    refine outer_congr (by norm_num) (fun y => by push_cast; ring) (fun y => by push_cast; ring)
      (fun y hy => by linarith [hy.1]) fun d hd c hc => ?_
    show _ = H4 Pt (c, d)
    unfold H4
    rw [slice_A2 (hW c d) hd.1 hd.2 hc.1 hc.2, pc_eval]
    exact ii_congr (by push_cast; ring) (by push_cast; ring) fun y =>
      ii_congr (by push_cast; ring) (by push_cast; ring) fun x => rfl
  · -- A3
    refine outer_congr (by norm_num) (fun y => by push_cast; ring) (fun y => by push_cast; ring)
      (fun x hx => by linarith [hx.1]) fun c hc d hd => ?_
    show _ = H4 Pt (c, d)
    unfold H4
    rw [slice_T3 (hW c d) hc.1 hc.2 hd.1 hd.2, pc_eval, pc_eval, pc_eval]
    refine rev3 ?_ ?_ ?_ <;>
      exact ii_congr (by push_cast; ring) (by push_cast; ring) fun y =>
        ii_congr (by push_cast; ring) (by push_cast; ring) fun x => rfl
  · -- A4
    refine outer_congr (by norm_num) (fun y => by push_cast; ring) (fun y => by push_cast; ring)
      (fun x hx => by linarith [hx.2]) fun c hc d hd => ?_
    show _ = H4 Pt (c, d)
    unfold H4
    rw [slice_T4 (hW c d) hc.1 hc.2 hd.1 hd.2, pc_eval, pc_eval, pc_eval]
    refine rev3 ?_ ?_ ?_ <;>
      exact ii_congr (by push_cast; ring) (by push_cast; ring) fun y =>
        ii_congr (by push_cast; ring) (by push_cast; ring) fun x => rfl

end XiPrime8845.Triple.Region

#print axioms XiPrime8845.Triple.Region.J4R_eq
