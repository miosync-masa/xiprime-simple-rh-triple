/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.HexLink

/-! # Region decomposition for `j3`

For `0 ≤ d ≤ 2` the set `shiftSet d = hexD ∩ (hexD − (d, −d))` is
`{d−1 ≤ y ≤ 1, max(−1, −1−y) ≤ x ≤ min(1−d, 1−y)}`.  The checker's four pieces are exactly the
sub-intervals of `y` on which the `max` and the `min` are given by one of their arguments.
`J3R_eq`: `J3R Pt = ∫₀¹ T3 + ∫₁² T3`, `T3 d = ∫_{shiftSet d} P̃(x,y)·P̃(x+d,y−d)·(d−2)`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region
open IntCheck IntCheck.Sem

theorem integral_indicator_Icc (a b : ℝ) (f : ℝ → ℝ) (h : a ≤ b) :
    ∫ x, (Icc a b).indicator f x = ∫ x in a..b, f x := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le h]

/-- integral over a region between two graphs (`y` outer) as an iterated integral. -/
theorem setIntegral_between {W : ℝ × ℝ → ℝ} (hW : Continuous W) {L U : ℝ → ℝ}
    (hL : Measurable L) (hU : Measurable U) {c e : ℝ} (hce : c ≤ e)
    (hLU : ∀ y ∈ Icc c e, L y ≤ U y) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hSK : {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)} ⊆ K) :
    ∫ z in {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)}, W z
      = ∫ y in c..e, ∫ x in L y..U y, W (x, y) := by
  set S : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 ∈ Icc c e ∧ z.1 ∈ Icc (L z.2) (U z.2)} with hS
  have mS : MeasurableSet S := by
    have : S = (Prod.snd ⁻¹' Icc c e) ∩ ({z : ℝ × ℝ | L z.2 ≤ z.1} ∩ {z : ℝ × ℝ | z.1 ≤ U z.2}) := by
      ext z; simp [hS, mem_Icc]
    rw [this]
    exact (measurableSet_Icc.preimage measurable_snd).inter
      ((measurableSet_le (hL.comp measurable_snd) measurable_fst).inter
        (measurableSet_le measurable_fst (hU.comp measurable_snd)))
  have hint : Integrable (S.indicator W) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff mS).2 ((hW.continuousOn.integrableOn_compact hK).mono_set hSK)
  have inner : ∀ y, ∫ x, S.indicator W (x, y)
      = (Icc c e).indicator (fun y => ∫ x in L y..U y, W (x, y)) y := by
    intro y
    by_cases hy : y ∈ Icc c e
    · rw [indicator_of_mem hy, ← integral_indicator_Icc _ _ _ (hLU y hy)]
      congr 1; funext x
      have : (x, y) ∈ S ↔ x ∈ Icc (L y) (U y) := ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
      rw [indicator_apply, indicator_apply]
      simp only [this]
    · rw [indicator_of_notMem hy]
      have : ∀ x, S.indicator W (x, y) = 0 := fun x => indicator_of_notMem (fun h => hy h.1) _
      simp [this]
  rw [← integral_indicator mS, Measure.volume_eq_prod, integral_prod_symm _ hint]
  simp only [inner]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hce]

theorem continuous_inner {W : ℝ × ℝ → ℝ} (hW : Continuous W) {L U : ℝ → ℝ}
    (hL : Continuous L) (hU : Continuous U) :
    Continuous fun y => ∫ x in L y..U y, W (x, y) := by
  have hu : Continuous (Function.uncurry fun (y x : ℝ) => W (x, y)) :=
    hW.comp (continuous_snd.prodMk continuous_fst)
  have key := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume) (a₀ := (0 : ℝ)) hu
  have hc : ∀ y : ℝ, Continuous fun x : ℝ => W (x, y) := fun y =>
    hW.comp (continuous_id.prodMk continuous_const)
  have e : ∀ y, ∫ x in L y..U y, W (x, y)
      = (∫ x in (0 : ℝ)..U y, W (x, y)) - ∫ x in (0 : ℝ)..L y, W (x, y) := fun y =>
    (intervalIntegral.integral_interval_sub_left ((hc y).intervalIntegrable _ _)
      ((hc y).intervalIntegrable _ _)).symm
  simp only [e]
  exact (key.comp (continuous_id.prodMk hU)).sub (key.comp (continuous_id.prodMk hL))

theorem mem_hexD {z : ℝ × ℝ} : z ∈ hexD ↔
    (-1 ≤ z.1 ∧ z.1 ≤ 1) ∧ (-1 ≤ z.2 ∧ z.2 ≤ 1) ∧ (-1 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 1) := by
  simp [hexD, abs_le]

def shiftSet (d : ℝ) : Set (ℝ × ℝ) := hexD ∩ {z | (z.1 + d, z.2 - d) ∈ hexD}

theorem shiftSet_eq {d : ℝ} (hd0 : 0 ≤ d) :
    shiftSet d = {z : ℝ × ℝ | z.2 ∈ Icc (d - 1) 1 ∧
      z.1 ∈ Icc (max (-1) (-1 - z.2)) (min (1 - d) (1 - z.2))} := by
  ext z
  simp only [shiftSet, mem_inter_iff, mem_hexD, mem_ofPred_eq, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩, ⟨⟨e1, e2⟩, ⟨f1, f2⟩, ⟨g1, g2⟩⟩⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  · rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩, ⟨r1, r2⟩⟩
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;> linarith

theorem slice_eq {W : ℝ × ℝ → ℝ} (hW : Continuous W) {d : ℝ} (hd0 : 0 ≤ d) (hd2 : d ≤ 2) :
    ∫ z in shiftSet d, W z
      = ∫ y in (d - 1)..1, ∫ x in (max (-1) (-1 - y))..(min (1 - d) (1 - y)), W (x, y) := by
  rw [shiftSet_eq hd0]
  refine setIntegral_between hW (L := fun y => max (-1) (-1 - y))
    (U := fun y => min (1 - d) (1 - y)) (by fun_prop) (by fun_prop) (by linarith) ?_
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) ?_
  · intro y hy
    exact max_le (le_min (by linarith) (by linarith [hy.2])) (le_min (by linarith [hy.1]) (by linarith))
  · rintro z ⟨⟨p1, p2⟩, q1, q2⟩
    have := max_le_iff.1 q1
    have := le_min_iff.1 q2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem slice_low {W : ℝ × ℝ → ℝ} (hW : Continuous W) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    ∫ z in shiftSet d, W z
      = (∫ y in (d - 1)..0, ∫ x in (-1 - y)..(1 - d), W (x, y))
        + ((∫ y in (0 : ℝ)..d, ∫ x in (-1 : ℝ)..(1 - d), W (x, y))
          + ∫ y in d..1, ∫ x in (-1 : ℝ)..(1 - y), W (x, y)) := by
  have hG : Continuous fun y => ∫ x in (max (-1) (-1 - y))..(min (1 - d) (1 - y)), W (x, y) :=
    continuous_inner hW (by fun_prop) (by fun_prop)
  rw [slice_eq hW hd0 (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable (d - 1) 0)
      (hG.intervalIntegrable 0 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable 0 d)
      (hG.intervalIntegrable d 1)]
  congr 1
  · refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le (by linarith)] at hy
    simp only [max_eq_right (show (-1 : ℝ) ≤ -1 - y by linarith [hy.2]),
      min_eq_left (show 1 - d ≤ 1 - y by linarith [hy.2])]
  · congr 1
    · refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le hd0] at hy
      simp only [max_eq_left (show -1 - y ≤ (-1 : ℝ) by linarith [hy.1]),
        min_eq_left (show 1 - d ≤ 1 - y by linarith [hy.2])]
    · refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le hd1] at hy
      simp only [max_eq_left (show -1 - y ≤ (-1 : ℝ) by linarith [hy.1]),
        min_eq_right (show 1 - y ≤ 1 - d by linarith [hy.1])]

theorem slice_high {W : ℝ × ℝ → ℝ} (hW : Continuous W) {d : ℝ} (hd1 : 1 ≤ d) (hd2 : d ≤ 2) :
    ∫ z in shiftSet d, W z = ∫ y in (d - 1)..1, ∫ x in (-1 : ℝ)..(1 - d), W (x, y) := by
  rw [slice_eq hW (by linarith) hd2]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le (by linarith)] at hy
  simp only [max_eq_left (show -1 - y ≤ (-1 : ℝ) by linarith [hy.1]),
    min_eq_left (show 1 - d ≤ 1 - y by linarith [hy.2])]

/-! ## link with the checker's pieces -/

theorem ii_congr {a b a' b' : ℝ} {f g : ℝ → ℝ} (ha : a = a') (hb : b = b')
    (h : ∀ y, f y = g y) : ∫ y in a..b, f y = ∫ y in a'..b', g y := by
  subst ha hb; simp only [h]

/-- the integrand of `j3` at fixed `d`. -/
def W3 (Pt : List (List Int)) (d : ℝ) (z : ℝ × ℝ) : ℝ :=
  PR Pt z.1 z.2 * PR Pt (z.1 + d) (z.2 - d) * (d - 2)

theorem W3_continuous (Pt : List (List Int)) (d : ℝ) : Continuous (W3 Pt d) := by
  have h1 := PR_continuous Pt
  have h2 : Continuous fun z : ℝ × ℝ => PR Pt (z.1 + d) (z.2 - d) :=
    h1.comp (by fun_prop : Continuous fun z : ℝ × ℝ => (z.1 + d, z.2 - d))
  exact (h1.mul h2).mul continuous_const

theorem pc3_eval (Pt : List (List Int)) (cv1 a1 b1 cv2 a2 b2 a3 b3 a4 b4 : Int) (d : ℝ) :
    pc3 Pt cv1 a1 b1 cv2 a2 b2 a3 b3 a4 b4 (d, ())
      = ∫ y in ((b3 : ℝ) + a3 * d)..((b4 : ℝ) + a4 * d),
          ∫ x in ((b1 : ℝ) + a1 * d + cv1 * y)..((b2 : ℝ) + a2 * d + cv2 * y), W3 Pt d (x, y) := by
  have hF : ∀ (cv a b : Int) (y : ℝ), lv2'.f (Gen.F IntCheck.o1 cv (IntCheck.lin1 a b)) (y, (d, ()))
      = (b : ℝ) + a * d + cv * y := by
    intro cv a b y
    have := F_sem lv1 cv (IntCheck.lin1 a b) y (d, ())
    rw [lin1_sem] at this
    exact this
  simp only [pc3, XYR, hF, lin1_sem, R3_sem, W3]

/-- the true `d`-slice of `j3`. -/
noncomputable def T3 (Pt : List (List Int)) (d : ℝ) : ℝ := ∫ z in shiftSet d, W3 Pt d z

theorem J3R_eq (Pt : List (List Int)) :
    J3R Pt = (∫ d in (0 : ℝ)..1, T3 Pt d) + ∫ d in (1 : ℝ)..2, T3 Pt d := by
  unfold J3R
  simp only [Int.cast_zero, Int.cast_one, Int.cast_ofNat]
  congr 1
  · refine intervalIntegral.integral_congr fun d hd => ?_
    rw [uIcc_of_le zero_le_one] at hd
    show _ = T3 Pt d
    unfold T3
    rw [slice_low (W3_continuous Pt d) hd.1 hd.2, pc3_eval, pc3_eval, pc3_eval]
    refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_) <;>
      exact ii_congr (by push_cast; ring) (by push_cast; ring) fun y =>
        ii_congr (by push_cast; ring) (by push_cast; ring) fun x => rfl
  · refine intervalIntegral.integral_congr fun d hd => ?_
    rw [uIcc_of_le (by norm_num)] at hd
    show _ = T3 Pt d
    unfold T3
    rw [slice_high (W3_continuous Pt d) hd.1 hd.2, pc3_eval]
    exact ii_congr (by push_cast; ring) (by push_cast; ring) fun y =>
      ii_congr (by push_cast; ring) (by push_cast; ring) fun x => rfl

end XiPrime8845.Triple.Region

#print axioms XiPrime8845.Triple.Region.J3R_eq
