/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Module.Basic

/-! The arithmetic ingredients for the triple-correlation support gate.
The logarithmic spacing lemma excludes the *near* off-diagonal only. -/

noncomputable section
open ArithmeticFunction Filter
open scoped Asymptotics

namespace RHTriple.PrimeArithmetic

private theorem log_gap_ordered {p q : ℕ} (hq : 0 < q) (hqp : q < p) :
    1 / (2 * Real.sqrt ((p : ℝ) * (q : ℝ))) ≤
      Real.log (p : ℝ) - Real.log (q : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp' : (0 : ℝ) < p := by exact_mod_cast (hq.trans hqp)
  have hsub : (1 : ℝ) ≤ (p : ℝ) - (q : ℝ) := by
    have h : ((q : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hqp
    linarith
  have hs : Real.sqrt ((p : ℝ) * (q : ℝ)) ^ 2 = (p : ℝ) * (q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hspos : 0 < Real.sqrt ((p : ℝ) * (q : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hbase : ((p : ℝ) - (q : ℝ)) / (p : ℝ) ≤
      Real.log (p : ℝ) - Real.log (q : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    rw [Real.log_div hq'.ne' hp'.ne'] at hh
    rw [sub_div, div_self hp'.ne']
    linarith
  apply le_trans _ hbase
  by_cases hfar : (2 : ℝ) * (q : ℝ) ≤ (p : ℝ)
  · have honep : (1 : ℝ) ≤ p := by exact_mod_cast (hq.trans hqp)
    have honeq : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hsqone : (1 : ℝ) ≤ Real.sqrt ((p : ℝ) * (q : ℝ)) := by
      have hmul : 1 ≤ (p : ℝ) * (q : ℝ) :=
        by simpa only [one_mul] using mul_le_mul honep honeq (by norm_num : (0 : ℝ) ≤ 1) hp'.le
      by_contra! hneg
      nlinarith [mul_pos hspos (sub_pos.mpr hneg)]
    calc
      1 / (2 * Real.sqrt ((p : ℝ) * (q : ℝ))) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ ≤ ((p : ℝ) - (q : ℝ)) / (p : ℝ) := by
        rw [le_div_iff₀ hp']
        linarith
  · have hclose : (p : ℝ) ≤ 2 * Real.sqrt ((p : ℝ) * (q : ℝ)) := by
      push Not at hfar
      have hcross := mul_le_mul_of_nonneg_left hfar.le hp'.le
      by_contra! hh
      nlinarith [mul_pos (sub_pos.mpr hh)
        (show 0 < (p : ℝ) + 2 * Real.sqrt ((p : ℝ) * (q : ℝ)) by positivity)]
    calc
      1 / (2 * Real.sqrt ((p : ℝ) * (q : ℝ))) ≤ 1 / (p : ℝ) :=
        one_div_le_one_div_of_le hp' hclose
      _ ≤ ((p : ℝ) - (q : ℝ)) / (p : ℝ) :=
        div_le_div_of_nonneg_right hsub hp'.le

/-- Distinct integer products are separated at the reciprocal geometric-mean scale. -/
theorem log_gap {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) :
    1 / (2 * Real.sqrt ((p : ℝ) * (q : ℝ))) ≤
      |Real.log (p : ℝ) - Real.log (q : ℝ)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_sub_comm, mul_comm (p : ℝ)]
    exact (log_gap_ordered hp h).trans (le_abs_self _)
  · exact (log_gap_ordered hq h).trans (le_abs_self _)

/-- A height cutoff combined with the product bound excludes all near
off-diagonal terms. In the hexagon application, `X` bounds the square root
of the product of the three prime powers, not their largest individual size. -/
theorem eq_of_log_gap {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {T B X : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hx : Real.sqrt ((p : ℝ) * (q : ℝ)) ≤ X) (hcut : 2 * B * X < T)
    (hnear : |Real.log (p : ℝ) - Real.log (q : ℝ)| ≤ B / T) : p = q := by
  by_contra hne
  have hs : 0 < Real.sqrt ((p : ℝ) * (q : ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast hp) (by exact_mod_cast hq)
  have hh := (log_gap hp hq hne).trans hnear
  have hmul := (div_le_div_iff₀ (show 0 < 2 * Real.sqrt ((p : ℝ) * (q : ℝ))
    by positivity) hT).1 hh
  have hcut' := (mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * B by positivity)).trans_lt hcut
  nlinarith

/-- The power-saving height frequency forced by a fixed hexagonal margin.
The hypothesis states the arithmetic `log(PQ)` bound after localization,
not the assertion that the original test-function support implies it. -/
theorem height_log_gap_of_margin {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q)
    {T eta : ℝ} (hT : 1 < T)
    (hmargin : Real.log (p : ℝ) + Real.log (q : ℝ) ≤ (2 - eta) * Real.log T) :
    T ^ (eta / 2) / 2 ≤ T * |Real.log (p : ℝ) - Real.log (q : ℝ)| := by
  have hT0 := zero_lt_one.trans hT
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← Real.log_mul hp'.ne' hq'.ne', ← Real.log_rpow hT0,
    Real.log_le_log_iff (mul_pos hp' hq') (Real.rpow_pos_of_pos hT0 _)] at hmargin
  have hs : Real.sqrt ((p : ℝ) * (q : ℝ)) ≤ T ^ (1 - eta / 2) := by
    calc
      _ ≤ Real.sqrt (T ^ (2 - eta)) := Real.sqrt_le_sqrt hmargin
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
        congr 1
        ring
  have hd : 2 * Real.sqrt ((p : ℝ) * (q : ℝ)) ≤ 2 * T ^ (1 - eta / 2) :=
    mul_le_mul_of_nonneg_left hs (by norm_num)
  have hg := (one_div_le_one_div_of_le
    (show 0 < 2 * Real.sqrt ((p : ℝ) * (q : ℝ)) by positivity) hd).trans
    (log_gap hp hq hne)
  have hpow : T ^ (eta / 2) * T ^ (1 - eta / 2) = T := by
    rw [← Real.rpow_add hT0, show eta / 2 + (1 - eta / 2) = 1 by ring, Real.rpow_one]
  calc
    _ = (T ^ (eta / 2) * T ^ (1 - eta / 2)) * (1 / (2 * T ^ (1 - eta / 2))) := by
      field_simp
    _ = T * (1 / (2 * T ^ (1 - eta / 2))) :=
      congrArg (· * (1 / (2 * T ^ (1 - eta / 2)))) hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hT0.le

private theorem prime_eq_of_dvd_pow {p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hd : p ∣ r ^ k) : p = r := by
  exact ((Nat.dvd_prime hr).1 (hp.dvd_of_dvd_pow hd)).resolve_left hp.ne_one

/-- In a nonzero three-prime-power diagonal, all three powers have the same prime base. -/
theorem diagonal_prime_powers {a b c : ℕ}
    (ha : vonMangoldt a ≠ 0) (hb : vonMangoldt b ≠ 0) (hc : vonMangoldt c ≠ 0)
    (heq : a * b = c) :
    ∃ p i j : ℕ, p.Prime ∧ 0 < i ∧ 0 < j ∧ a = p ^ i ∧ b = p ^ j ∧ c = p ^ (i + j) := by
  obtain ⟨p, i, hp, hi, hpa⟩ := (isPrimePow_nat_iff a).1 (vonMangoldt_ne_zero_iff.1 ha)
  obtain ⟨q, j, hq, hj, hqb⟩ := (isPrimePow_nat_iff b).1 (vonMangoldt_ne_zero_iff.1 hb)
  obtain ⟨r, k, hr, _, hrc⟩ := (isPrimePow_nat_iff c).1 (vonMangoldt_ne_zero_iff.1 hc)
  have hh : p ^ i * q ^ j = r ^ k := by rw [hpa, hqb, hrc, heq]
  have hpd : p ∣ r ^ k := by
    rw [← hh]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hi.ne') _
  have hqd : q ∣ r ^ k := by
    rw [← hh]
    exact dvd_mul_of_dvd_right (dvd_pow_self q hj.ne') _
  have hpr := prime_eq_of_dvd_pow hp hr hpd
  have hqr := prime_eq_of_dvd_pow hq hr hqd
  subst p
  subst q
  exact ⟨r, i, j, hr, hi, hj, hpa.symm, hqb.symm, by rw [pow_add, hpa, hqb, heq]⟩

set_option maxHeartbeats 1000000 in
/-- After the two positive exponents are summed geometrically, the
three-prime-power diagonal is dominated by this convergent series. -/
theorem diagonal_majorant_summable :
    Summable (fun p : ℕ => if 2 ≤ p then Real.log (p : ℝ) ^ 3 / ((p : ℝ) - 1) ^ 2 else 0) := by
  have hsum : Summable (fun p : ℕ => (p : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.2 (by norm_num)
  refine Summable.of_nonneg_of_le (f := fun p : ℕ => 864 * (p : ℝ) ^ (-3 / 2 : ℝ)) ?_ ?_
    (hsum.mul_left 864)
  · intro p
    split_ifs with hp
    · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
      exact div_nonneg (pow_nonneg (Real.log_nonneg hp') _) (sq_nonneg _)
    · exact le_rfl
  · intro p
    split_ifs with hp
    · have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
      have hp0 : (0 : ℝ) < p := by linarith
      have hlog : Real.log (p : ℝ) ≤ 6 * (p : ℝ) ^ (1 / 6 : ℝ) := by
        have hh := Real.log_le_rpow_div hp0.le (show (0 : ℝ) < 1 / 6 by norm_num)
        linarith
      have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
      have hcube : Real.log (p : ℝ) ^ 3 ≤ 216 * (p : ℝ) ^ (1 / 2 : ℝ) := calc
        _ ≤ (6 * (p : ℝ) ^ (1 / 6 : ℝ)) ^ 3 := by gcongr
        _ = 216 * (p : ℝ) ^ (1 / 2 : ℝ) := by
          rw [mul_pow, ← Real.rpow_mul_natCast hp0.le]
          norm_num
      have hden : ((p : ℝ) / 2) ^ 2 ≤ ((p : ℝ) - 1) ^ 2 := by
        gcongr
        linarith
      calc
        _ ≤ (216 * (p : ℝ) ^ (1 / 2 : ℝ)) / ((p : ℝ) / 2) ^ 2 :=
          div_le_div₀ (by positivity) hcube (by positivity) hden
        _ = 864 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
          have he : (p : ℝ) ^ (1 / 2 : ℝ) =
              (p : ℝ) ^ (-3 / 2 : ℝ) * (p : ℝ) ^ 2 := by
            rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_add hp0]
            norm_num
          rw [he]
          field_simp
          ring
    · positivity

/-- The actual normalized mass of a same-prime diagonal term. The exponents
are offset by one so that both powers are genuinely nontrivial. -/
def diagonalMass (p i j : ℕ) : ℝ :=
  if 2 ≤ p then Real.log (p : ℝ) ^ 3 / (p : ℝ) ^ (i + j + 2) else 0

theorem diagonalMass_nonneg (p i j : ℕ) : 0 ≤ diagonalMass p i j := by
  unfold diagonalMass
  split_ifs with hp
  · have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    exact div_nonneg (pow_nonneg (Real.log_nonneg hp') _) (by positivity)
  · exact le_rfl

theorem diagonalMass_eq_vonMangoldt {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    diagonalMass p i j =
      vonMangoldt (p ^ (i + 1)) * vonMangoldt (p ^ (j + 1)) *
      vonMangoldt (p ^ (i + j + 2)) / (p : ℝ) ^ (i + j + 2) := by
  simp only [diagonalMass, if_pos hp.two_le, vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    vonMangoldt_apply_prime hp]
  ring

set_option maxHeartbeats 1000000 in
/-- Uniform absolute summability of the three-prime-power product diagonal. -/
theorem diagonalMass_summable : Summable (fun x : ℕ × ℕ × ℕ => diagonalMass x.1 x.2.1 x.2.2) := by
  apply (summable_prod_of_nonneg (f := fun x : ℕ × ℕ × ℕ => diagonalMass x.1 x.2.1 x.2.2)
    (fun x => diagonalMass_nonneg x.1 x.2.1 x.2.2)).2
  have hg (p : ℕ) (hp : 2 ≤ p) :
      Summable (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) ∧
      (∑' n : ℕ, ((p : ℝ)⁻¹) ^ n) = (1 - (p : ℝ)⁻¹)⁻¹ := by
    have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    have h₁ : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have h₂ : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp'
    exact ⟨summable_geometric_of_lt_one h₁ h₂, tsum_geometric_of_lt_one h₁ h₂⟩
  have hfactor (p i j : ℕ) (hp : 2 ≤ p) :
      diagonalMass p i j =
        (Real.log (p : ℝ) ^ 3 / (p : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ i) * ((p : ℝ)⁻¹) ^ j := by
    have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    simp only [diagonalMass, if_pos hp, pow_add, inv_pow]
    field_simp
  have hpair (p : ℕ) (hp : 2 ≤ p) :
      Summable (fun y : ℕ × ℕ => diagonalMass p y.1 y.2) := by
    apply (summable_prod_of_nonneg (f := fun y : ℕ × ℕ => diagonalMass p y.1 y.2)
      (fun y => diagonalMass_nonneg p y.1 y.2)).2
    simp only [hfactor _ _ _ hp, tsum_mul_left]
    constructor
    · exact fun _ => (hg _ hp).1.mul_left _
    · exact ((hg _ hp).1.mul_left _).mul_right _
  constructor
  · intro p
    by_cases hp : 2 ≤ p
    · exact hpair p hp
    · simp [diagonalMass, hp]
  · convert diagonal_majorant_summable using 1
    ext p
    by_cases hp : 2 ≤ p
    · have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
      have hp0 : (0 : ℝ) < p := by linarith
      have hne : (p : ℝ) - 1 ≠ 0 := by linarith
      have hne' : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
        have h := inv_lt_one_of_one_lt₀ hp'
        linarith
      rw [(hpair p hp).tsum_prod, if_pos hp]
      simp only [hfactor _ _ _ hp, tsum_mul_left, tsum_mul_right, (hg _ hp).2]
      field_simp
    · simp [diagonalMass, hp]

/-- On the diagonal `c = a*b`, the product of the three square-root
denominators is `a*b`. The zero terms are left in place. -/
def vonMangoldtDiagonal (x : ℕ × ℕ) : ℝ :=
  vonMangoldt x.1 * vonMangoldt x.2 * vonMangoldt (x.1 * x.2) /
    ((x.1 * x.2 : ℕ) : ℝ)

theorem vonMangoldtDiagonal_nonneg (x : ℕ × ℕ) : 0 ≤ vonMangoldtDiagonal x :=
  div_nonneg (mul_nonneg (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
    vonMangoldt_nonneg) (Nat.cast_nonneg _)

set_option maxHeartbeats 1000000 in
/-- Reindex the actual product diagonal by the common prime and the two
positive exponents. The reindexing is injective on the nonzero support. -/
theorem vonMangoldtDiagonal_summable : Summable vonMangoldtDiagonal := by
  classical
  let S : Set (ℕ × ℕ) := {x | vonMangoldt x.1 ≠ 0 ∧ vonMangoldt x.2 ≠ 0 ∧
    vonMangoldt (x.1 * x.2) ≠ 0}
  have hparam (x : S) : ∃ y : ℕ × ℕ × ℕ, y.1.Prime ∧
      x.val.1 = y.1 ^ (y.2.1 + 1) ∧ x.val.2 = y.1 ^ (y.2.2 + 1) ∧
      x.val.1 * x.val.2 = y.1 ^ (y.2.1 + y.2.2 + 2) := by
    obtain ⟨p, i, j, hp, hi, hj, h₁, h₂, h₃⟩ :=
      diagonal_prime_powers x.property.1 x.property.2.1 x.property.2.2 rfl
    cases i with
    | zero => omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        refine ⟨(p, i, j), hp, h₁, h₂, ?_⟩
        rw [h₃, show i.succ + j.succ = i + j + 2 by omega]
  let f (x : S) : ℕ × ℕ × ℕ := (hparam x).choose
  have hspec (x : S) := (hparam x).choose_spec
  have hinj : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Prod.ext
    · rw [(hspec x).2.1, (hspec y).2.1]
      change (f x).1 ^ ((f x).2.1 + 1) = (f y).1 ^ ((f y).2.1 + 1)
      rw [hh]
    · rw [(hspec x).2.2.1, (hspec y).2.2.1]
      change (f x).1 ^ ((f x).2.2 + 1) = (f y).1 ^ ((f y).2.2 + 1)
      rw [hh]
  have hsum : Summable (fun x : S => vonMangoldtDiagonal x.val) := by
    apply (diagonalMass_summable.comp_injective hinj).congr
    intro x
    change diagonalMass (f x).1 (f x).2.1 (f x).2.2 = vonMangoldtDiagonal x.val
    rw [diagonalMass_eq_vonMangoldt (hspec x).1, vonMangoldtDiagonal]
    have h₁ := congrArg vonMangoldt (hspec x).2.1
    have h₂ := congrArg vonMangoldt (hspec x).2.2.1
    have h₃ := congrArg vonMangoldt (hspec x).2.2.2
    have hc := congrArg (fun n : ℕ => (n : ℝ)) (hspec x).2.2.2
    rw [Nat.cast_pow] at hc
    exact congrArg₂ (· / ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h₁.symm h₂.symm) h₃.symm)
      hc.symm
  apply ((summable_subtype_iff_indicator (f := vonMangoldtDiagonal) (s := S)).1 hsum).congr
  intro x
  by_cases hx : x ∈ S
  · simp [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    by_cases h₁ : vonMangoldt x.1 = 0
    · simp [vonMangoldtDiagonal, h₁]
    by_cases h₂ : vonMangoldt x.2 = 0
    · simp [vonMangoldtDiagonal, h₂]
    by_cases h₃ : vonMangoldt (x.1 * x.2) = 0
    · simp [vonMangoldtDiagonal, h₃]
    exact False.elim (hx ⟨h₁, h₂, h₃⟩)

/-- A cutoff of the all-prime diagonal, weighted by a bounded kernel, has a
bound that is independent of the cutoff. -/
theorem diagonal_weighted_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset (ℕ × ℕ)) (K : ℕ × ℕ → E) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ x ∈ s, ‖K x‖ ≤ A) :
    ‖∑ x ∈ s, vonMangoldtDiagonal x • K x‖ ≤ A * (∑' x, vonMangoldtDiagonal x) := by
  calc
    _ ≤ ∑ x ∈ s, ‖vonMangoldtDiagonal x • K x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, A * vonMangoldtDiagonal x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_smul, Real.norm_of_nonneg (vonMangoldtDiagonal_nonneg x), mul_comm A]
      exact mul_le_mul_of_nonneg_left (hK x hx) (vonMangoldtDiagonal_nonneg x)
    _ = A * (∑ x ∈ s, vonMangoldtDiagonal x) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (vonMangoldtDiagonal_summable.sum_le_tsum s (fun x _ => vonMangoldtDiagonal_nonneg x)) hA

/-- In particular an eventually uniform `O(T)` kernel bound makes the
three-prime-power product diagonal `o(T log T)`. The analytic kernel
estimate must be supplied separately. -/
theorem diagonal_weighted_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ → Finset (ℕ × ℕ)) (K : ℝ → ℕ × ℕ → E) {A : ℝ} (hA : 0 ≤ A)
    (hK : ∀ᶠ T in atTop, ∀ x ∈ s T, ‖K T x‖ ≤ A * T) :
    (fun T => ∑ x ∈ s T, vonMangoldtDiagonal x • K T x) =o[atTop]
      (fun T : ℝ => T * Real.log T) := by
  rw [Asymptotics.isLittleO_iff]
  intro eps heps
  have hl := Real.tendsto_log_atTop.eventually_ge_atTop ((A * (∑' x, vonMangoldtDiagonal x)) / eps)
  filter_upwards [hK, hl, eventually_ge_atTop (1 : ℝ)] with T hKT hlT hT
  have ht : 0 ≤ T := zero_le_one.trans hT
  have hb := (div_le_iff₀ heps).mp hlT
  rw [Real.norm_of_nonneg (mul_nonneg ht (Real.log_nonneg hT))]
  calc
    _ ≤ (A * T) * (∑' x, vonMangoldtDiagonal x) :=
      diagonal_weighted_norm_le (s T) (K T) (mul_nonneg hA ht) hKT
    _ = T * (A * (∑' x, vonMangoldtDiagonal x)) := by ring
    _ ≤ T * (Real.log T * eps) := mul_le_mul_of_nonneg_left hb ht
    _ = _ := by ring

/-- Arithmetic summation of the far off-diagonal: a polynomial mass
envelope and a uniform sufficiently rapid kernel decay give `o(T log T)`.
The actual Fourier-localization and kernel bounds are separate hypotheses. -/
theorem offDiagonal_weighted_isLittleO {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : ℝ → Finset ι) (P Q : ι → ℕ) (W : ℝ → ι → ℝ)
    (K : ℝ → ι → E) {eta d k B C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hpower : d ≤ eta / 2 * k)
    (hcut : ∀ᶠ T in atTop, ∀ x ∈ s T, 0 < P x ∧ 0 < Q x ∧ P x ≠ Q x ∧
      Real.log (P x : ℝ) + Real.log (Q x : ℝ) ≤ (2 - eta) * Real.log T)
    (hmass : ∀ᶠ T in atTop, ∑ x ∈ s T, |W T x| ≤ B * T ^ d)
    (hK : ∀ᶠ T in atTop, ∀ x ∈ s T, ‖K T x‖ ≤ C * T *
      (T * |Real.log (P x : ℝ) - Real.log (Q x : ℝ)|) ^ (-k)) :
    (fun T => ∑ x ∈ s T, W T x • K T x) =o[atTop] (fun T : ℝ => T * Real.log T) := by
  rw [Asymptotics.isLittleO_iff]
  intro eps heps
  let A := C * (1 / 2 : ℝ) ^ (-k)
  have hA : 0 ≤ A := mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (A * B / eps)
  filter_upwards [hcut, hmass, hK, hlog, eventually_gt_atTop (1 : ℝ)]
    with T hcutT hmassT hKT hlogT hT
  have ht := zero_lt_one.trans hT
  have hbound (x : ι) (hx : x ∈ s T) : ‖K T x‖ ≤ A * T * T ^ (-d) := by
    obtain ⟨hp, hq, hne, hm⟩ := hcutT x hx
    have hg := height_log_gap_of_margin hp hq hne hT hm
    have hlower : 0 < T ^ (eta / 2) / 2 := by positivity
    have hdec := Real.rpow_le_rpow_of_nonpos hlower hg (neg_nonpos.mpr hk)
    have hscale : T ^ (eta / 2 * -k) ≤ T ^ (-d) :=
      Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
    calc
      _ ≤ C * T * (T * |Real.log (P x : ℝ) - Real.log (Q x : ℝ)|) ^ (-k) := hKT x hx
      _ ≤ C * T * (T ^ (eta / 2) / 2) ^ (-k) :=
          mul_le_mul_of_nonneg_left hdec (mul_nonneg hC ht.le)
      _ = A * T * T ^ (eta / 2 * -k) := by
          rw [show T ^ (eta / 2) / 2 = (1 / 2 : ℝ) * T ^ (eta / 2) by ring,
            Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul ht.le]
          unfold A
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale (mul_nonneg hA ht.le)
  have hd : 0 ≤ A * T * T ^ (-d) :=
    mul_nonneg (mul_nonneg hA ht.le) (Real.rpow_nonneg ht.le _)
  have hab := (div_le_iff₀ heps).mp hlogT
  have hcancel : T ^ (-d) * T ^ d = 1 := by
    rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
  rw [Real.norm_of_nonneg (mul_nonneg ht.le (Real.log_nonneg hT.le))]
  calc
    _ ≤ ∑ x ∈ s T, ‖W T x • K T x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s T, (A * T * T ^ (-d)) * |W T x| := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_smul, Real.norm_eq_abs, mul_comm (A * T * T ^ (-d))]
      exact mul_le_mul_of_nonneg_left (hbound x hx) (abs_nonneg _)
    _ = (A * T * T ^ (-d)) * (∑ x ∈ s T, |W T x|) := (Finset.mul_sum ..).symm
    _ ≤ (A * T * T ^ (-d)) * (B * T ^ d) := mul_le_mul_of_nonneg_left hmassT hd
    _ = T * (A * B) := by
      calc
        _ = T * (A * B) * (T ^ (-d) * T ^ d) := by ring
        _ = _ := by rw [hcancel, mul_one]
    _ ≤ T * (Real.log T * eps) := mul_le_mul_of_nonneg_left hab ht.le
    _ = _ := by ring

#print axioms log_gap
#print axioms eq_of_log_gap
#print axioms height_log_gap_of_margin
#print axioms diagonal_prime_powers
#print axioms diagonalMass_summable
#print axioms vonMangoldtDiagonal_summable
#print axioms diagonal_weighted_isLittleO
#print axioms offDiagonal_weighted_isLittleO

end RHTriple.PrimeArithmetic
