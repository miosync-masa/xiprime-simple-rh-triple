/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairPrimeL1
import RHTriple.PairGammaMain

/-! On a nonzero prime pulse the other, opposite-frequency gamma
kernel is uniformly bounded: it is away from gamma's central peak.
This uses the actual 1/x tail, not an assumed rapid decrease. -/

noncomputable section
open Complex MeasureTheory Filter Finset

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

theorem pairPrimeFactor_zero_near_origin {k : ℝ → ℂ} {R T B s : ℝ}
    (hR : ∀ x, k x ≠ 0 → |x| ≤ R)
    (hT : 0 < T) (hcut : R < T/4) (hs : |s| ≤ 1/4) :
    primeFactor (dilate k T) B s = 0 := by
  unfold primeFactor
  rw [sum_eq_zero]
  · simp
  · intro n hn
    have hpos := (mem_Ioc.mp hn).1
    by_cases h1 : n = 1
    · simp [h1]
    have hn2 : 2 ≤ n := by omega
    have hl := log_two_le_log hn2
    have H (z : ℝ) (hz : (1:ℝ)/2 ≤ |z|) : dilate k T (z-s) = 0 := by
      by_contra! hnz
      have hx : k (T*(z-s)) ≠ 0 := fun h => hnz (by simp [dilate,h])
      have hh := hR _ hx
      rw [abs_mul,abs_of_pos hT] at hh
      have hb : (1:ℝ)/4 ≤ |z-s| := by
        have h := abs_sub_abs_le_abs_sub z s
        linarith only [h,hz,hs]
      have hprod := mul_le_mul_of_nonneg_left hb hT.le
      linarith only [hh,hprod,hcut]
    rw [H _ (hl.trans (le_abs_self _)), H _ (by rw [abs_neg]; exact hl.trans (le_abs_self _)),
      add_zero,mul_zero]

theorem pairGammaFactor_bounded_away {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {R T s : ℝ}
    (hR : ∀ x, k x ≠ 0 → |x| ≤ R)
    (hT : 0 < T) (hcut : R < T/8) (hs : 1/4 ≤ |s|) :
    ‖gammaFactor (dilate k T) s‖ ≤ 40*(∫ x, ‖k x‖) := by
  have hprod := mul_le_mul_of_nonneg_left hs hT.le
  have hh : |-(T*s)|-R ≥ T/8 := by
    rw [abs_neg, abs_mul, abs_of_pos hT]
    linarith only [hcut,hprod]
  have hd : R < |-(T*s)| := by linarith only [hh,hT]
  have hTail := scaledGamma_tail hk hkc hT hR hd
  rw [gammaFactor_dilate k hT,norm_mul,norm_real,Real.norm_of_nonneg hT.le]
  let C := 5*(∫ x, ‖k x‖)
  have hc : 0 ≤ C := mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)
  have hExp : Real.exp (-(|-(T*s)|-R)/(4*T)) ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith only [hd]) (by positivity))
  calc
    _ ≤ T*(C*(Real.exp (-(|-(T*s)|-R)/(4*T))/(|-(T*s)|-R))) :=
      mul_le_mul_of_nonneg_left hTail hT.le
    _ ≤ T*(C*(1/(T/8))) := by
      gcongr
    _ = _ := by unfold C; field_simp <;> ring

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pairPrimeFactor_zero_near_origin
#print axioms XiPrime8845.RHTriple.pairGammaFactor_bounded_away
