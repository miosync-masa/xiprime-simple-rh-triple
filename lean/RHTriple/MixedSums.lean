/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedArithmetic
import RHTriple.MixedKernel
import RHTriple.MixedSupport

/-! Summation of the actual mixed kernels. Keep the two orderings of the
opposite-sign prime pair separate; the equal-index term is not an error. -/

noncomputable section
open Complex Filter Finset
open scoped Asymptotics

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

def onePrimeSum (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s : Bool) (N : ℕ) (T : ℝ) : ℂ :=
  ∑ n ∈ Icc 2 N, primeWeight n • onePrimeGamma k Φ T (Real.log T) (signedLog s n)

def sameSignPrimeSum (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s : Bool) (N : ℕ) (T : ℝ) : ℂ :=
  ∑ n ∈ Icc 2 N, ∑ m ∈ Icc 2 N, (primeWeight n * primeWeight m) •
    twoPrimeGamma k Φ T (Real.log T) (signedLog s n) (signedLog s m)

private def orderedArgs (reverse : Bool) (u v : ℝ) : ℝ × ℝ := if reverse then (v,u) else (u,v)

def oppositeSignOrderedSum (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s reverse : Bool) (N : ℕ) (T : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, ∑ m ∈ Ioc n N, (primeWeight n * primeWeight m) •
    let z := orderedArgs reverse (signedLog s n) (signedLog (!s) m)
    twoPrimeGamma k Φ T (Real.log T) z.1 z.2

private theorem abs_same_signed_sum {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (s : Bool) :
    |signedLog s n + signedLog s m| = Real.log n + Real.log m := by
  have h : 0 ≤ Real.log n + Real.log m := by linarith [log_two_le_log hn, log_two_le_log hm]
  cases s
  · change |-Real.log n + -Real.log m| = _
    rw [← neg_add, abs_neg, abs_of_nonneg h]
  · exact abs_of_nonneg h

private theorem abs_opposite_ordered_sum {n m : ℕ} (hn : 0 < n) (hnm : n < m) (s rev : Bool) :
    let z := orderedArgs rev (signedLog s n) (signedLog (!s) m)
    |z.1+z.2| = Real.log m - Real.log n := by
  have h : 0 ≤ Real.log m - Real.log n := sub_nonneg.mpr
    (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnm.le))
  cases s <;> cases rev <;> simp [orderedArgs, signedLog] <;>
    first | rw [show -Real.log n+Real.log m = Real.log m-Real.log n by ring, abs_of_nonneg h]
          | rw [show Real.log n+-Real.log m = -(Real.log m-Real.log n) by ring, abs_neg, abs_of_nonneg h]
          | rw [show -Real.log m+Real.log n = -(Real.log m-Real.log n) by ring, abs_neg, abs_of_nonneg h]
          | rw [show Real.log m+-Real.log n = Real.log m-Real.log n by ring, abs_of_nonneg h]

private theorem littleO_of_height_power {f : ℝ → ℂ} {p C : ℝ} (hp : p < 1) (_hC : 0 ≤ C)
    (h : ∀ᶠ T in atTop, ‖f T‖ ≤ C*(T^p*Real.log T)) :
    f =o[atTop] (fun T => T*Real.log T) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hpow := (tendsto_rpow_atTop (sub_pos.mpr hp)).eventually_ge_atTop (C/ε)
  filter_upwards [h, hpow, eventually_gt_atTop (1:ℝ)] with T hT hP h1
  have ht : 0 < T := by linarith
  have hl := Real.log_nonneg h1.le
  have hmul : T^p * T^(1-p) = T := by rw [← Real.rpow_add ht, show p+(1-p)=1 by ring, Real.rpow_one]
  rw [Real.norm_of_nonneg (mul_nonneg ht.le hl)]
  calc
    _ ≤ C*(T^p*Real.log T) := hT
    _ = (T^p*Real.log T)*C := by ring
    _ ≤ (T^p*Real.log T)*(T^(1-p)*ε) := mul_le_mul_of_nonneg_left ((div_le_iff₀ hε).1 hP) (by positivity)
    _ = _ := by rw [show (T^p*Real.log T)*(T^(1-p)*ε)=(T^p*T^(1-p))*Real.log T*ε by ring, hmul]; ring

theorem onePrimeSum_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (s : Bool) {p : ℝ} (hp : p < 1)
    (N : ℝ → ℕ) (hN : ∀ᶠ T in atTop, 1 ≤ N T ∧ (N T : ℝ) ≤ T^p) :
    (fun T => onePrimeSum k Φ s (N T) T) =o[atTop] (fun T => T*Real.log T) := by
  obtain ⟨R₀, hR₀⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs (u : ℝ) (hu : k u ≠ 0) : |u| ≤ R := (hR₀ u hu).trans (le_max_left _ _)
  obtain ⟨C,hC,hK⟩ := onePrimeGamma_bound hk hkc hΦ hΦc hR hs
  apply littleO_of_height_power hp (show 0 ≤ 4*C by positivity)
  filter_upwards [hN, eventually_ge_atTop (1:ℝ), eventually_ge_atTop (16*(R+1)),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T ⟨hN1,hNB⟩ hT hSep hL
  let L := Real.log T
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := by linarith
  have hcoeff : C*(1+L)/L^2 ≤ 2*C := by
    rw [div_le_iff₀ (sq_pos_of_pos hL0)]
    have hh : 1+L ≤ 2*L^2 := by nlinarith [sq_nonneg (L-1)]
    nlinarith only [mul_le_mul_of_nonneg_left hh hC]
  unfold onePrimeSum
  calc
    _ ≤ ∑ n ∈ Icc 2 (N T), (2*C)*(primeWeight n / Real.log n) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      have hn2 := (mem_Icc.mp hn).1
      have hn0 : 0 < n := by omega
      have hlog := log_two_le_log hn2
      have hlog0 : 0 < Real.log n := by linarith
      have hgap : 8*(R+1) ≤ T*|signedLog s n| := by
        rw [abs_signedLog hn0]
        nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ T by linarith),hSep]
      rw [norm_smul, Real.norm_of_nonneg (primeWeight_nonneg n)]
      refine (mul_le_mul_of_nonneg_left (hK T L _ hT hL0 hgap) (primeWeight_nonneg n)).trans ?_
      rw [abs_signedLog hn0]
      calc
        _ = (C*(1+L)/L^2)*(primeWeight n / Real.log n) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (div_nonneg (primeWeight_nonneg n) hlog0.le)
    _ ≤ (2*C)*(2*Real.sqrt (N T)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (single_prime_log_sum_le _) (by positivity)
    _ ≤ _ := by
      have hns : (1:ℝ) ≤ N T := by exact_mod_cast hN1
      have hsN : Real.sqrt (N T) ≤ (N T:ℝ) := calc
        _ ≤ Real.sqrt ((N T : ℝ)^2) := Real.sqrt_le_sqrt (by
          nlinarith only [mul_nonneg (Nat.cast_nonneg (N T) : 0 ≤ (N T:ℝ)) (sub_nonneg.mpr hns)])
        _ = _ := Real.sqrt_sq (Nat.cast_nonneg (N T))
      have hnB := hsN.trans hNB
      have hTL : T^p ≤ T^p*L := le_mul_of_one_le_right (by positivity) hL1
      nlinarith only [mul_le_mul_of_nonneg_left (hnB.trans hTL) hC]

private theorem logNat_le_height {T p : ℝ} {n N : ℕ} (hT : 0 < T)
    (hn : 0 < n) (hnN : n ≤ N) (hN : (N : ℝ) ≤ T^p) : Real.log n ≤ p*Real.log T := by
  rw [← Real.log_rpow hT]
  exact Real.log_le_log (by exact_mod_cast hn) ((show (n:ℝ) ≤ N by exact_mod_cast hnN).trans hN)

private theorem coeffLogSquare_le {C L l : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hl : 0 ≤ l) (hlL : l ≤ L) : (C/L^2)*l^2 ≤ C := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hL)]
  exact mul_le_mul_of_nonneg_left (by gcongr) hC

theorem sameSignPrimeSum_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (s : Bool) {p : ℝ} (hp : p < 1)
    (N : ℝ → ℕ) (hN : ∀ᶠ T in atTop, 1 ≤ N T ∧ (N T : ℝ) ≤ T^p) :
    (fun T => sameSignPrimeSum k Φ s (N T) T) =o[atTop] (fun T => T*Real.log T) := by
  obtain ⟨R₀, hR₀⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs (u : ℝ) (hu : k u ≠ 0) : |u| ≤ R := (hR₀ u hu).trans (le_max_left _ _)
  obtain ⟨C,hC,hK⟩ := twoPrimeGamma_bound hk hkc hΦ hΦc hR hs
  apply littleO_of_height_power hp (show 0 ≤ 4*C by positivity)
  filter_upwards [hN, eventually_ge_atTop (1:ℝ), eventually_ge_atTop (8*(R+1)),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T ⟨hN1,hNB⟩ hT hSep hL
  let L := Real.log T
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := by linarith
  have ht : 0 < T := by linarith
  have hNp : 0 < N T := by omega
  have hnL := logNat_le_height ht hNp le_rfl hNB
  have hnlog0 : 0 ≤ Real.log (N T) := Real.log_nonneg (by exact_mod_cast hN1)
  have hnlogL : Real.log (N T) ≤ L := hnL.trans (mul_le_of_le_one_left hL0.le hp.le)
  unfold sameSignPrimeSum
  calc
    _ ≤ ∑ n ∈ Icc 2 (N T), ∑ m ∈ Icc 2 (N T),
        (C/L^2)*(primeWeight n * primeWeight m/(Real.log n+Real.log m)) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro n hn
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro m hm
      have hn2 := (mem_Icc.mp hn).1
      have hm2 := (mem_Icc.mp hm).1
      have hlogs : 1 ≤ Real.log n + Real.log m := by linarith [log_two_le_log hn2, log_two_le_log hm2]
      have hgap : 8*(R+1) ≤ T*|signedLog s n+signedLog s m| := by
        rw [abs_same_signed_sum hn2 hm2]
        exact hSep.trans (le_mul_of_one_le_right ht.le hlogs)
      have hw := mul_nonneg (primeWeight_nonneg n) (primeWeight_nonneg m)
      rw [norm_smul, Real.norm_of_nonneg hw]
      refine (mul_le_mul_of_nonneg_left (hK T L _ _ ht hL0 hgap) hw).trans_eq ?_
      rw [abs_same_signed_sum hn2 hm2]
      simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ (C/L^2)*(4*(N T:ℝ)*(Real.log (N T))^2) := by
      simp_rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (same_sign_prime_log_sum_le _) (by positivity)
    _ = 4*(N T:ℝ)*((C/L^2)*(Real.log (N T))^2) := by ring
    _ ≤ 4*(N T:ℝ)*C := mul_le_mul_of_nonneg_left (coeffLogSquare_le hC hL0 hnlog0 hnlogL) (by positivity)
    _ ≤ _ := by
      have hnT := hNB.trans (le_mul_of_one_le_right (Real.rpow_nonneg ht.le _) hL1)
      nlinarith only [mul_le_mul_of_nonneg_left hnT hC]

theorem oppositeSignOrderedSum_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (s rev : Bool) {p : ℝ} (hp : p < 1)
    (N : ℝ → ℕ) (hN : ∀ᶠ T in atTop, 1 ≤ N T ∧ (N T : ℝ) ≤ T^p) :
    (fun T => oppositeSignOrderedSum k Φ s rev (N T) T) =o[atTop] (fun T => T*Real.log T) := by
  obtain ⟨R₀, hR₀⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs (u : ℝ) (hu : k u ≠ 0) : |u| ≤ R := (hR₀ u hu).trans (le_max_left _ _)
  obtain ⟨C,hC,hK⟩ := twoPrimeGamma_bound hk hkc hΦ hΦc hR hs
  apply littleO_of_height_power hp (show 0 ≤ 12*C by positivity)
  have hheight := (tendsto_rpow_atTop (sub_pos.mpr hp)).eventually_ge_atTop (16*(R+1))
  filter_upwards [hN, eventually_gt_atTop (1:ℝ), hheight,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T ⟨hN1,hNB⟩ hT hSep hL
  let L := Real.log T
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := by linarith
  have ht : 0 < T := by linarith
  have hNp : 0 < N T := by omega
  have hnL := logNat_le_height ht hNp le_rfl hNB
  have hnlog0 : 0 ≤ Real.log (N T) := Real.log_nonneg (by exact_mod_cast hN1)
  have hnlogL : Real.log (N T) ≤ L := hnL.trans (mul_le_of_le_one_left hL0.le hp.le)
  unfold oppositeSignOrderedSum
  calc
    _ ≤ ∑ n ∈ Icc 1 (N T), ∑ m ∈ Ioc n (N T),
        (C/L^2)*(primeWeight n * primeWeight m/(Real.log m-Real.log n)) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro n hn
      apply (norm_sum_le _ _).trans
      apply sum_le_sum; intro m hm
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hnm := (mem_Ioc.mp hm).1
      have hm0 := hn0.trans hnm
      let z := orderedArgs rev (signedLog s n) (signedLog (!s) m)
      have hD : |z.1+z.2| = Real.log m - Real.log n := abs_opposite_ordered_sum hn0 hnm s rev
      have hlog : 0 ≤ Real.log m - Real.log n := sub_nonneg.mpr
        (Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnm.le))
      have hmargin : Real.log m + Real.log n ≤ (2-(2-2*p))*Real.log T := by
        nlinarith only [logNat_le_height ht hn0 (mem_Icc.mp hn).2 hNB,
          logNat_le_height ht hm0 (mem_Ioc.mp hm).2 hNB]
      have hgap' := height_log_gap_of_margin hm0 hn0 hnm.ne' hT hmargin
      rw [show (2-2*p)/2=1-p by ring, abs_of_nonneg hlog] at hgap'
      have hgap : 8*(R+1) ≤ T*|z.1+z.2| := by rw [hD]; linarith
      have hw := mul_nonneg (primeWeight_nonneg n) (primeWeight_nonneg m)
      change ‖(primeWeight n*primeWeight m) • twoPrimeGamma k Φ T L z.1 z.2‖ ≤ _
      rw [norm_smul, Real.norm_of_nonneg hw]
      refine (mul_le_mul_of_nonneg_left (hK T L _ _ ht hL0 hgap) hw).trans_eq ?_
      rw [hD]
      simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ (C/L^2)*((Real.log (N T))^2*((N T:ℝ)*(10+2*Real.log (N T)))) := by
      simp_rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (ordered_prime_log_gap_sum_le _) (by positivity)
    _ = ((C/L^2)*(Real.log (N T))^2)*((N T:ℝ)*(10+2*Real.log (N T))) := by ring
    _ ≤ C*((N T:ℝ)*(10+2*Real.log (N T))) :=
      mul_le_mul_of_nonneg_right (coeffLogSquare_le hC hL0 hnlog0 hnlogL) (by positivity)
    _ ≤ C*(T^p*(12*L)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul hNB (by linarith) (by positivity) (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

/-- The cutoff supplied by the actual hexagon satisfies the height condition
of the three summed estimates; it is not an extra arithmetic hypothesis. -/
theorem mixedCutoff_height {η : ℝ} (hη : η ≤ 1) :
    ∀ᶠ T in atTop, 1 ≤ ⌊T ^ (1-η/4)⌋₊ ∧ (⌊T ^ (1-η/4)⌋₊ : ℝ) ≤ T ^ (1-η/4) := by
  have hp : 0 < 1-η/4 := by linarith
  filter_upwards [(tendsto_rpow_atTop hp).eventually_ge_atTop 1] with T hT
  exact ⟨(Nat.le_floor_iff (by linarith : 0 ≤ T^(1-η/4))).2 (by simpa using hT),
    Nat.floor_le (by linarith)⟩

theorem mixedSums_hex_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (s rev : Bool) :
    let N := fun T : ℝ => ⌊T ^ (1-η/4)⌋₊
    ((fun T => onePrimeSum k Φ s (N T) T) =o[atTop] (fun T => T*Real.log T)) ∧
    ((fun T => sameSignPrimeSum k Φ s (N T) T) =o[atTop] (fun T => T*Real.log T)) ∧
    ((fun T => oppositeSignOrderedSum k Φ s rev (N T) T) =o[atTop] (fun T => T*Real.log T)) := by
  have hp : 1-η/4 < 1 := by linarith
  exact ⟨onePrimeSum_isLittleO hk hkc hΦ hΦc s hp _ (mixedCutoff_height hη1),
    sameSignPrimeSum_isLittleO hk hkc hΦ hΦc s hp _ (mixedCutoff_height hη1),
    oppositeSignOrderedSum_isLittleO hk hkc hΦ hΦc s rev hp _ (mixedCutoff_height hη1)⟩

def oppositeSignOffDiagSum (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s : Bool) (N : ℕ) (T : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, if n = m then 0 else
    (primeWeight n * primeWeight m) • twoPrimeGamma k Φ T (Real.log T) (signedLog s n) (signedLog (!s) m)

private theorem split_unordered_sum (N : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, if n=m then 0 else F n m) =
      (∑ n ∈ Icc 1 N, ∑ m ∈ Ioc n N, F n m) +
      ∑ n ∈ Icc 1 N, ∑ m ∈ Ioc n N, F m n := by
  have h (n m : ℕ) : (if n=m then 0 else F n m) =
      (if n<m then F n m else 0)+(if m<n then F n m else 0) := by
    rcases lt_trichotomy n m with h | rfl | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · simp
    · simp [h, h.ne', not_lt_of_ge h.le]
  have hreduce (G : ℕ → ℕ → ℂ) :
      (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, if n<m then G n m else 0) =
        ∑ n ∈ Icc 1 N, ∑ m ∈ Ioc n N, G n m := by
    apply sum_congr rfl; intro n hn
    rw [← sum_filter]
    congr 1
    ext m
    have h1 := (mem_Icc.mp hn).1
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  simp_rw [h, sum_add_distrib]
  rw [hreduce F]
  congr 1
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, if n<m then F m n else 0 := sum_comm
    _ = _ := hreduce (fun n m => F m n)

theorem oppositeSignOffDiagSum_eq (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s : Bool) (N : ℕ) (T : ℝ) :
    oppositeSignOffDiagSum k Φ s N T =
      oppositeSignOrderedSum k Φ s false N T + oppositeSignOrderedSum k Φ (!s) true N T := by
  unfold oppositeSignOffDiagSum oppositeSignOrderedSum
  rw [split_unordered_sum]
  congr 1
  apply sum_congr rfl; intro n _
  apply sum_congr rfl; intro m _
  simp [orderedArgs, mul_comm (primeWeight m)]

theorem oppositeSignOffDiagSum_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (s : Bool) :
    (fun T => oppositeSignOffDiagSum k Φ s ⌊T ^ (1-η/4)⌋₊ T) =o[atTop] (fun T => T*Real.log T) := by
  simp_rw [oppositeSignOffDiagSum_eq]
  exact (mixedSums_hex_isLittleO hk hkc hΦ hΦc hη hη1 s false).2.2.add
    (mixedSums_hex_isLittleO hk hkc hΦ hΦc hη hη1 (!s) true).2.2

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.onePrimeSum_isLittleO
#print axioms XiPrime8845.RHTriple.sameSignPrimeSum_isLittleO
#print axioms XiPrime8845.RHTriple.oppositeSignOrderedSum_isLittleO
#print axioms XiPrime8845.RHTriple.mixedSums_hex_isLittleO
#print axioms XiPrime8845.RHTriple.oppositeSignOffDiagSum_isLittleO
