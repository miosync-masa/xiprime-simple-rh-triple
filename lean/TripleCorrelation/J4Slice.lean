/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.J3Region

/-! # Region decomposition for `j4`, part 1: the `(x, y)` slices at fixed shift `(c, d)`

For `c ≤ 0 ≤ d`, `0 ≤ c + d`, `-2 ≤ c`, `d ≤ 2` the set `shift2 c d = hexD ∩ (hexD + (c, d))` is
`{d−1 ≤ y ≤ 1, max(−1, c+d−1−y) ≤ x ≤ min(1+c, 1−y)}`.  The lower bound switches at `y = c+d`,
the upper bound at `y = −c`; the four lemmas `slice_A1`, `slice_A2`, `slice_T3`, `slice_T4` are
the four possible orders of these break points inside the triangle `0 ≤ d ≤ 2`, `−d ≤ c ≤ 0`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region

def shift2 (c d : ℝ) : Set (ℝ × ℝ) := hexD ∩ {w | (w.1 - c, w.2 - d) ∈ hexD}

theorem shift2_eq {c d : ℝ} (hc : c ≤ 0) (hd : 0 ≤ d) (hs : 0 ≤ c + d) :
    shift2 c d = {w : ℝ × ℝ | w.2 ∈ Icc (d - 1) 1 ∧
      w.1 ∈ Icc (max (-1) (c + d - 1 - w.2)) (min (1 + c) (1 - w.2))} := by
  ext w
  simp only [shift2, mem_inter_iff, mem_hexD, mem_ofPred_eq, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩, ⟨⟨e1, e2⟩, ⟨f1, f2⟩, ⟨g1, g2⟩⟩⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  · rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩, ⟨r1, r2⟩⟩
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;> linarith

variable {W : ℝ × ℝ → ℝ} {c d : ℝ}

theorem slice2_eq (hW : Continuous W) (hc : c ≤ 0) (hc2 : -2 ≤ c) (hd : 0 ≤ d) (hd2 : d ≤ 2)
    (hs : 0 ≤ c + d) :
    ∫ w in shift2 c d, W w = ∫ y in (d - 1)..1,
      ∫ x in (max (-1) (c + d - 1 - y))..(min (1 + c) (1 - y)), W (x, y) := by
  rw [shift2_eq hc hd hs]
  refine setIntegral_between hW (L := fun y => max (-1) (c + d - 1 - y))
    (U := fun y => min (1 + c) (1 - y)) (by fun_prop) (by fun_prop) (by linarith) ?_
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) ?_
  · intro y hy
    exact max_le (le_min (by linarith) (by linarith [hy.2]))
      (le_min (by linarith [hy.1]) (by linarith))
  · rintro z ⟨⟨p1, p2⟩, q1, q2⟩
    have := max_le_iff.1 q1
    have := le_min_iff.1 q2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem contG (hW : Continuous W) (c d : ℝ) :
    Continuous fun y => ∫ x in (max (-1) (c + d - 1 - y))..(min (1 + c) (1 - y)), W (x, y) :=
  continuous_inner hW (by fun_prop) (by fun_prop)

theorem slice_A1 (hW : Continuous W) (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hc1 : -d ≤ c) (hc2 : c ≤ -1) :
    ∫ w in shift2 c d, W w = ∫ y in (d - 1)..1, ∫ x in (-1 : ℝ)..(1 + c), W (x, y) := by
  rw [slice2_eq hW (by linarith) (by linarith) (by linarith) hd2 (by linarith)]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le (by linarith)] at hy
  simp only [max_eq_left (show c + d - 1 - y ≤ (-1 : ℝ) by linarith [hy.1]),
    min_eq_left (show 1 + c ≤ 1 - y by linarith [hy.2])]

theorem slice_A2 (hW : Continuous W) (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hc1 : 1 - d ≤ c) (hc2 : c ≤ 0) :
    ∫ w in shift2 c d, W w = ∫ y in (d - 1)..1, ∫ x in (c + d - 1 - y)..(1 - y), W (x, y) := by
  rw [slice2_eq hW hc2 (by linarith) (by linarith) hd2 (by linarith)]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le (by linarith)] at hy
  simp only [max_eq_right (show (-1 : ℝ) ≤ c + d - 1 - y by linarith [hy.2]),
    min_eq_right (show 1 - y ≤ 1 + c by linarith [hy.1])]

theorem slice_T3 (hW : Continuous W) (hc1 : -1 ≤ c) (hc2 : c ≤ 0) (hd1 : -2 * c ≤ d)
    (hd2 : d ≤ 1 - c) :
    ∫ w in shift2 c d, W w
      = (∫ y in (d - 1)..(-c), ∫ x in (c + d - 1 - y)..(1 + c), W (x, y))
        + ((∫ y in (-c)..(c + d), ∫ x in (c + d - 1 - y)..(1 - y), W (x, y))
          + ∫ y in (c + d)..1, ∫ x in (-1 : ℝ)..(1 - y), W (x, y)) := by
  have hG := contG hW c d
  rw [slice2_eq hW hc2 (by linarith) (by linarith) (by linarith) (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable (d - 1) (-c))
      (hG.intervalIntegrable (-c) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable (-c) (c + d))
      (hG.intervalIntegrable (c + d) 1)]
  congr 1
  · refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le (by linarith)] at hy
    simp only [max_eq_right (show (-1 : ℝ) ≤ c + d - 1 - y by linarith [hy.2]),
      min_eq_left (show 1 + c ≤ 1 - y by linarith [hy.2])]
  · congr 1
    · refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le (by linarith)] at hy
      simp only [max_eq_right (show (-1 : ℝ) ≤ c + d - 1 - y by linarith [hy.2]),
        min_eq_right (show 1 - y ≤ 1 + c by linarith [hy.1])]
    · refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le (by linarith)] at hy
      simp only [max_eq_left (show c + d - 1 - y ≤ (-1 : ℝ) by linarith [hy.1]),
        min_eq_right (show 1 - y ≤ 1 + c by linarith [hy.1])]

theorem slice_T4 (hW : Continuous W) (hc1 : -1 ≤ c) (hc2 : c ≤ 0) (hd1 : -c ≤ d)
    (hd2 : d ≤ -2 * c) :
    ∫ w in shift2 c d, W w
      = (∫ y in (d - 1)..(c + d), ∫ x in (c + d - 1 - y)..(1 + c), W (x, y))
        + ((∫ y in (c + d)..(-c), ∫ x in (-1 : ℝ)..(1 + c), W (x, y))
          + ∫ y in (-c)..1, ∫ x in (-1 : ℝ)..(1 - y), W (x, y)) := by
  have hG := contG hW c d
  rw [slice2_eq hW hc2 (by linarith) (by linarith) (by linarith) (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable (d - 1) (c + d))
      (hG.intervalIntegrable (c + d) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable (c + d) (-c))
      (hG.intervalIntegrable (-c) 1)]
  congr 1
  · refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le (by linarith)] at hy
    simp only [max_eq_right (show (-1 : ℝ) ≤ c + d - 1 - y by linarith [hy.2]),
      min_eq_left (show 1 + c ≤ 1 - y by linarith [hy.2])]
  · congr 1
    · refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le (by linarith)] at hy
      simp only [max_eq_left (show c + d - 1 - y ≤ (-1 : ℝ) by linarith [hy.1]),
        min_eq_left (show 1 + c ≤ 1 - y by linarith [hy.2])]
    · refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le (by linarith)] at hy
      simp only [max_eq_left (show c + d - 1 - y ≤ (-1 : ℝ) by linarith [hy.1]),
        min_eq_right (show 1 - y ≤ 1 + c by linarith [hy.1])]

end XiPrime8845.Triple.Region

#print axioms XiPrime8845.Triple.Region.slice_T3
#print axioms XiPrime8845.Triple.Region.slice_T4
