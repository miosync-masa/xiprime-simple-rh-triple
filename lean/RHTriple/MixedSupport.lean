/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PrimeKernel

/-! Each coordinate of the strict hexagon is individually subcritical.
These cutoff and spacing statements do not require the gamma estimates. -/

noncomputable section
open Complex MeasureTheory Filter

namespace XiPrime8845.RHTriple

def signedLog (positive : Bool) (n : ℕ) : ℝ :=
  if positive then Real.log n else -Real.log n

theorem abs_signedLog {n : ℕ} (hn : 0 < n) (s : Bool) : |signedLog s n| = Real.log n := by
  have h := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn)
  cases s <;> simp [signedLog, abs_of_nonneg h]

theorem frequencyShift_hex_bound {L η : ℝ} {p : ℝ × ℝ} (hL : 0 ≤ L)
    (hhex : |p.1|+|p.2|+|p.1+p.2| ≤ 2-η) (i : Fin 3) :
    |frequencyShift L i p| ≤ (1-η/2)*L := by
  have h0 : |p.1| ≤ |p.1+p.2|+|p.2| := by
    simpa only [add_sub_cancel_right] using abs_sub (p.1+p.2) p.2
  have h1 : |p.2| ≤ |p.1+p.2|+|p.1| := by
    simpa only [add_sub_cancel_left] using abs_sub (p.1+p.2) p.1
  have h2 := abs_add_le p.1 p.2
  fin_cases i
  · change |L*p.1| ≤ _
    rw [abs_mul, abs_of_nonneg hL, mul_comm (1-η/2)]
    exact mul_le_mul_of_nonneg_left (by linarith) hL
  · change |L*p.2| ≤ _
    rw [abs_mul, abs_of_nonneg hL, mul_comm (1-η/2)]
    exact mul_le_mul_of_nonneg_left (by linarith) hL
  · change |-(L*p.1+L*p.2)| ≤ _
    rw [abs_neg, ← mul_add, abs_mul, abs_of_nonneg hL, mul_comm (1-η/2)]
    exact mul_le_mul_of_nonneg_left (by linarith) hL

theorem prime_cutoff_eventually {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hkc : HasCompactSupport k) {η : ℝ} (hη : 0 < η)
    (hΦ : ∀ p : ℝ × ℝ, Φ p ≠ 0 → |p.1|+|p.2|+|p.1+p.2| ≤ 2-η) :
    ∀ᶠ T in atTop, ∀ (p : ℝ × ℝ), Φ p ≠ 0 → ∀ (i : Fin 3) (n : ℕ) (s : Bool),
      0 < n → dilate k T (signedLog s n-frequencyShift (Real.log T) i p) ≠ 0 →
      n ≤ ⌊T ^ (1-η/4)⌋₊ := by
  obtain ⟨R, hR⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop R,
    Real.tendsto_log_atTop.eventually_ge_atTop (4/η)] with T hT hTR hLT
  intro p hp i n s hn hnon
  have ht : 0 < T := by linarith
  have hl := Real.log_nonneg hT.le
  let x := signedLog s n - frequencyShift (Real.log T) i p
  have hx : k (T*x) ≠ 0 := fun he => hnon (by change _ * k (T*x) = 0; rw [he,mul_zero])
  have hraw := hR _ hx
  rw [abs_mul, abs_of_pos ht] at hraw
  have hgap : |x| ≤ 1 := ((le_div_iff₀ ht).2 (by simpa only [mul_comm] using hraw)).trans
    ((div_le_one ht).2 hTR)
  have hfreq := frequencyShift_hex_bound hl (hΦ p hp) i
  have hh : Real.log n ≤ |x| + |frequencyShift (Real.log T) i p| := by
    rw [← abs_signedLog hn s]
    unfold x
    simpa only [sub_add_cancel] using abs_add_le
      (signedLog s n-frequencyShift (Real.log T) i p) (frequencyShift (Real.log T) i p)
  have heta := (div_le_iff₀ hη).1 hLT
  have hbound : Real.log n ≤ (1-η/4)*Real.log T := by nlinarith only [hh, hgap, hfreq, heta]
  rw [← Real.log_rpow ht] at hbound
  exact (Nat.le_floor_iff (Real.rpow_nonneg ht.le _)).2
    ((Real.log_le_log_iff (by exact_mod_cast hn) (Real.rpow_pos_of_pos ht _)).1 hbound)

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.prime_cutoff_eventually
