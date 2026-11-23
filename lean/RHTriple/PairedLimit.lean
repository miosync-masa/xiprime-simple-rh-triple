/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.FocusedLimit
import RHTriple.PrimePairWeight

/-! The actual equal-index opposite-sign pair has the weighted line
limit in (3.49)–(3.50). Extending the line integral to one is harmless
because the test is supported strictly inside the hexagon. -/

noncomputable section
open Complex MeasureTheory Filter Topology Finset

namespace XiPrime8845.RHTriple

def pairProfile (Φ : ℝ × ℝ → ℂ) (s : Bool) (u : ℝ) : ℂ :=
  if s then Φ (u,-u) else Φ (-u,u)

def pairLine (Φ : ℝ × ℝ → ℂ) (s : Bool) : ℂ :=
  ∫ u in (0:ℝ)..1, pairProfile Φ s u * (u:ℂ)

private theorem pairProfile_support {Φ : ℝ × ℝ → ℂ} {η : ℝ}
    (_hη : 0 < η) (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) (s : Bool) :
    ∀ u, pairProfile Φ s u ≠ 0 → |u| ≤ 1-η/2 := by
  intro u hu
  cases s
  · have h := hhex (-u,u) (by simpa [pairProfile] using hu)
    simp only [abs_neg, neg_add_cancel, abs_zero, add_zero] at h
    linarith
  · have h := hhex (u,-u) (by simpa [pairProfile] using hu)
    simp only [abs_neg, add_neg_cancel, abs_zero, add_zero] at h
    linarith

private theorem opposite_signedLog (s : Bool) (n : ℕ) : signedLog (!s) n = -signedLog s n := by
  cases s <;> simp [signedLog]

private theorem log_signedLog_pair (Φ : ℝ × ℝ → ℂ) (s : Bool) (L : ℝ) (n : ℕ) :
    Φ (signedLog s n/L, -(signedLog s n/L)) = pairProfile Φ s (Real.log n/L) := by
  cases s <;> simp [pairProfile, signedLog, neg_div]

private def pairIndex (d L : ℝ) : Finset ℕ := Ioc 0 ⌊Real.exp (d*L)⌋₊

private def averagePaired (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (d T : ℝ) (s : Bool) : ℂ :=
  (∑ n ∈ pairIndex d (Real.log T), (pairedWeight n:ℂ) *
    planeProduct (focusedTest Φ (T*Real.log T) (signedLog s n/Real.log T)) k k
      (normalizedGamma k T))/(Real.log T:ℂ)^2

theorem pairedPrimeDiagonal_normalized_eq {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (d : ℝ) {T : ℝ} (hT : 1 < T) (s : Bool) :
    pairedPrimeDiagonal k Φ s ⌊T^d⌋₊ T / ((T*Real.log T : ℝ):ℂ) =
      averagePaired k Φ d T s := by
  let L := Real.log T
  have ht : 0 < T := by linarith
  have htc : (T:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hlc : (L:ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT).ne'
  have hi : Icc 1 ⌊T^d⌋₊ = pairIndex d L := by
    unfold pairIndex L
    rw [show Real.exp (d*Real.log T) = T^d by rw [Real.rpow_def_of_pos ht, mul_comm]]
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  unfold pairedPrimeDiagonal averagePaired
  rw [hi]
  simp_rw [opposite_signedLog s, pairedKernel_rescale hk hkc hΦ hΦc hT,
    primeWeight_sq_eq_pairedWeight, real_smul]
  let F (n : ℕ) := planeProduct (focusedTest Φ (T*L) (signedLog s n/L)) k k (normalizedGamma k T)
  change (∑ n ∈ pairIndex d L, (pairedWeight n : ℂ) * (((T/L : ℝ):ℂ) * F n)) /
      ((T*L : ℝ):ℂ) = (∑ n ∈ pairIndex d L, (pairedWeight n:ℂ)*F n)/(L:ℂ)^2
  calc
    _ = (((T/L:ℝ):ℂ)*(∑ n ∈ pairIndex d L, (pairedWeight n:ℂ)*F n))/((T*L:ℝ):ℂ) := by
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro n _
      ring
    _ = _ := by push_cast; field_simp

private def modelPaired (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (d T : ℝ) (s : Bool) : ℂ :=
  ((∑ n ∈ pairIndex d (Real.log T), (pairedWeight n:ℂ)*pairProfile Φ s (Real.log n/Real.log T))/
    (Real.log T:ℂ)^2)*heightTripleMass k

theorem averagePaired_sub_model_tendsto {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {d : ℝ} (hd : 0 < d) (s : Bool) :
    Tendsto (fun T => averagePaired k Φ d T s - modelPaired k Φ d T s) atTop (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := primePairMass_eventually_bounded hd
  rw [Metric.tendsto_nhds]
  intro ε hε
  let e := ε/(2*(1+C))
  have he : 0 < e := div_pos hε (by positivity)
  filter_upwards [Real.tendsto_log_atTop.eventually hCb, eventually_gt_atTop (1:ℝ),
    paired_plane_uniform hk hkc hΦ hΦc e he] with T hMass ht hErr
  let L := Real.log T
  have hl : 0 < L := Real.log_pos ht
  let K (n : ℕ) := planeProduct (focusedTest Φ (T*L) (signedLog s n/L)) k k (normalizedGamma k T) -
    pairProfile Φ s (Real.log n/L)*heightTripleMass k
  have KE (n : ℕ) : ‖K n‖ ≤ e := by
    simpa only [K, log_signedLog_pair] using hErr (signedLog s n/L)
  have hE : averagePaired k Φ d T s - modelPaired k Φ d T s =
      (∑ n ∈ pairIndex d L, (pairedWeight n:ℂ)*K n)/(L:ℂ)^2 := by
    unfold averagePaired modelPaired K L
    rw [div_mul_eq_mul_div, ← sub_div, sum_mul, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    ring
  rw [dist_eq_norm, sub_zero, hE, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hl.le]
  have hm : (∑ n ∈ pairIndex d L, pairedWeight n)/L^2 ≤ C := hMass
  have hnorm : ‖∑ n ∈ pairIndex d L, (pairedWeight n:ℂ)*K n‖ ≤
      e * ∑ n ∈ pairIndex d L, pairedWeight n := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pairedWeight_nonneg n), mul_comm e]
    exact mul_le_mul_of_nonneg_left (KE n) (pairedWeight_nonneg n)
  calc
    _ ≤ e * ((∑ n ∈ pairIndex d L, pairedWeight n)/L^2) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hnorm (by positivity)
    _ ≤ e*C := mul_le_mul_of_nonneg_left hm he.le
    _ < ε := by
      unfold e
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2*(1+C))]
      nlinarith only [hε, mul_nonneg hε.le hC]

theorem pairedPrimeDiagonal_normalized_tendsto {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) (s : Bool) :
    let d := 1-η/4
    Tendsto (fun T => pairedPrimeDiagonal k Φ s ⌊T^d⌋₊ T / ((T*Real.log T : ℝ):ℂ))
      atTop (𝓝 (pairLine Φ s * heightTripleMass k)) := by
  let d := 1-η/4
  have hd : 0 < d := by dsimp [d]; linarith
  have hd1 : d ≤ 1 := by dsimp [d]; linarith
  have hc : ContDiff ℝ 1 (pairProfile Φ s) := by
    cases s
    · change ContDiff ℝ 1 (fun u : ℝ => Φ (-u,u))
      exact hΦ.comp (by fun_prop)
    · change ContDiff ℝ 1 (fun u : ℝ => Φ (u,-u))
      exact hΦ.comp (by fun_prop)
  have hS := pairProfile_support hη hhex s
  have hcc := Zeta23.hasCompactSupport_of_support_subset_abs hS
  have hs (u : ℝ) (hu : d ≤ u) : pairProfile Φ s u = 0 := by
    by_contra h
    linarith only [le_abs_self u, hS u h, hu, hη, show d=1-η/4 from rfl]
  have hI : (∫ u in (0:ℝ)..d, pairProfile Φ s u*(u:ℂ)) = pairLine Φ s := by
    unfold pairLine
    have H : Continuous (fun u : ℝ => pairProfile Φ s u * (u:ℂ)) :=
      hc.continuous.mul Complex.continuous_ofReal
    have hadd : (∫ u in (0:ℝ)..d, pairProfile Φ s u*(u:ℂ)) +
        (∫ u in d..1, pairProfile Φ s u*(u:ℂ)) =
        (∫ u in (0:ℝ)..1, pairProfile Φ s u*(u:ℂ)) :=
      intervalIntegral.integral_add_adjacent_intervals (H.intervalIntegrable _ _) (H.intervalIntegrable _ _)
    rw [← hadd]
    have hz : (∫ u in d..1, pairProfile Φ s u*(u:ℂ)) = 0 := by
      rw [intervalIntegral.integral_of_le hd1]
      have h (u : ℝ) (hu : u ∈ Set.Ioc d 1) : pairProfile Φ s u*(u:ℂ) = 0 := by
        rw [hs u hu.1.le, zero_mul]
      exact setIntegral_eq_zero_of_forall_eq_zero h
    rw [hz, add_zero]
  have h := primePairWeight_complex_tendsto hc hcc hd hs
  rw [hI] at h
  have hmodel : Tendsto (fun T => modelPaired k Φ d T s) atTop
      (𝓝 (pairLine Φ s * heightTripleMass k)) :=
    (h.comp Real.tendsto_log_atTop).mul_const _
  have H := (averagePaired_sub_model_tendsto hk hkc hΦ.continuous hΦc hd s).add hmodel
  rw [zero_add] at H
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
  rw [sub_add_cancel, pairedPrimeDiagonal_normalized_eq hk hkc hΦ.continuous hΦc d ht]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pairedPrimeDiagonal_normalized_eq
#print axioms XiPrime8845.RHTriple.averagePaired_sub_model_tendsto
#print axioms XiPrime8845.RHTriple.pairedPrimeDiagonal_normalized_tendsto
