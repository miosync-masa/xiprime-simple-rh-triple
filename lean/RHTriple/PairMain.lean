/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairRemainder
import RHTriple.ZetaScale

/-! The two-slot main term in actual dyadic ζ-count units. Separate
height profiles are permitted, so the collapsed slot retains h². -/

noncomputable section
open Complex MeasureTheory Filter Topology
open scoped Asymptotics

namespace XiPrime8845.RHTriple
open Zeta23

def pairFrequencyMain (Q : ℝ → ℂ) : ℂ :=
  Q 0 + ∫ u : ℝ, Q u*((|u|:ℝ):ℂ)

private theorem pair_remainder_normalized {f : ℝ → ℂ}
    (h : f =o[atTop] (fun T => T*Real.log T)) :
    Tendsto (fun T => f T / ((T*Real.log T:ℝ):ℂ)) atTop (𝓝 0) := by
  have hh : f =o[atTop] (fun T => ((T*Real.log T:ℝ):ℂ)) :=
    h.norm_right.congr_right (fun T => (Complex.norm_real (T*Real.log T)).symm)
    |>.of_norm_right
  exact hh.tendsto_div_nhds_zero

private theorem pair_littleO_from_normalized {F : ℝ → ℂ} {a : ℂ}
    (h : Tendsto (fun T => F T / ((T*Real.log T : ℝ):ℂ)) atTop (𝓝 a)) :
    (fun T => F T - a*((T*Real.log T : ℝ):ℂ)) =o[atTop] (fun T => T*Real.log T) := by
  have hne : ∀ᶠ T : ℝ in atTop, ((T*Real.log T : ℝ):ℂ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact_mod_cast mul_ne_zero (show T ≠ 0 by linarith) (Real.log_pos hT).ne'
  have hsub := h.sub_const a
  rw [sub_self] at hsub
  have H : (fun T => F T - a*((T*Real.log T : ℝ):ℂ)) =o[atTop]
      (fun T => ((T*Real.log T : ℝ):ℂ)) := by
    refine Asymptotics.isLittleO_of_tendsto' (hne.mono fun T ht he => (ht he).elim)
      (hsub.congr' ?_)
    filter_upwards [hne] with T hT
    change F T / ((T*Real.log T : ℝ):ℂ)-a =
      (F T-a*((T*Real.log T : ℝ):ℂ))/((T*Real.log T : ℝ):ℂ)
    rw [sub_div, mul_div_cancel_right₀ _ hT]
  apply Asymptotics.IsLittleO.of_norm_right
  exact H.norm_right.congr_right fun T => Complex.norm_real (T*Real.log T)

theorem zeta_smoothed_pair_main_count (hRH : RiemannHypothesis)
    {a b Q : ℝ → ℂ} (ha : ContDiff ℝ 2 a) (hca : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hcb : HasCompactSupport b)
    (hQ : ContDiff ℝ 1 Q) (hcQ : HasCompactSupport Q) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hs : ∀ t, Q t ≠ 0 → |t| ≤ c) :
    (fun T => smoothedPair a b Q T - pairFrequencyMain Q *
      (∫ r : ℝ, paperFT a r*paperFT b r) * (Zeta23.Ncount T (2*T):ℂ))
      =o[atTop] (fun T => T*Real.log T) := by
  let d := (c+1)/2
  have hd : 0 < d := by unfold d; linarith
  have hcd : c < d := by unfold d; linarith
  have hd1 : d < 1 := by unfold d; linarith
  have G := pairGamma_normalized_tendsto ha hca hb hcb hQ.continuous hcQ
  have P := pairPrime_normalized_tendsto ha.continuous hca hb.continuous hcb hQ hcQ hd hd1
    (fun t ht => by by_contra h; exact (not_le_of_gt hcd) (ht.trans (hs t h)))
  have R := smoothedPair_sub_survivors_isLittleO hRH ha hca hb hcb hQ.continuous hcQ hcd hd hd1 hs
  have H := (pair_remainder_normalized R).add (G.add P)
  rw [zero_add, ← add_mul, ← pairFrequencyMain] at H
  have H' : Tendsto (fun T => smoothedPair a b Q T / ((T*Real.log T:ℝ):ℂ)) atTop
      (𝓝 (pairFrequencyMain Q * pairHeightMass a b)) := by
    refine H.congr' (Eventually.of_forall fun T => ?_)
    rw [← add_div, ← add_div, sub_add_cancel]
  have J := pair_littleO_from_normalized H'
  let A := pairFrequencyMain Q*(∫ r : ℝ, paperFT a r*paperFT b r)
  have K := zetaDyadicCount_sub_scale_isLittleO.const_mul_left A
  refine (J.sub K).congr_left ?_
  intro T
  change smoothedPair a b Q T - pairFrequencyMain Q * pairHeightMass a b*((T*Real.log T:ℝ):ℂ) -
    A*((Zeta23.Ncount T (2*T):ℂ)-(zetaMainScale T:ℂ)) = _
  unfold A zetaMainScale
  rw [← pairHeightMass_eq_heightIntegral ha hca hb hcb]
  push_cast
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem zeta_smoothed_pair_main_count_square_left (hRH : RiemannHypothesis)
    {k Q : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hQ : ContDiff ℝ 1 Q) (hcQ : HasCompactSupport Q) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hs : ∀ t, Q t ≠ 0 → |t| ≤ c) :
    (fun T => smoothedPair (heightSquareProfile k) k Q T - pairFrequencyMain Q *
      (∫ r : ℝ, (paperFT k r)^3) * (Zeta23.Ncount T (2*T):ℂ))
      =o[atTop] (fun T => T*Real.log T) := by
  simpa only [paperFT_heightSquareProfile hk hkc, ← pow_succ _ 2] using
    (zeta_smoothed_pair_main_count hRH (heightSquareProfile_contDiff hk hkc)
      (heightSquareProfile_compact hkc) hk hkc hQ hcQ hc hc1 hs)

theorem zeta_smoothed_pair_main_count_square_right (hRH : RiemannHypothesis)
    {k Q : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hQ : ContDiff ℝ 1 Q) (hcQ : HasCompactSupport Q) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hs : ∀ t, Q t ≠ 0 → |t| ≤ c) :
    (fun T => smoothedPair k (heightSquareProfile k) Q T - pairFrequencyMain Q *
      (∫ r : ℝ, (paperFT k r)^3) * (Zeta23.Ncount T (2*T):ℂ))
      =o[atTop] (fun T => T*Real.log T) := by
  simpa only [paperFT_heightSquareProfile hk hkc, ← pow_succ' _ 2] using
    (zeta_smoothed_pair_main_count hRH hk hkc (heightSquareProfile_contDiff hk hkc)
      (heightSquareProfile_compact hkc) hQ hcQ hc hc1 hs)

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.zeta_smoothed_pair_main_count
#print axioms XiPrime8845.RHTriple.zeta_smoothed_pair_main_count_square_left
#print axioms XiPrime8845.RHTriple.zeta_smoothed_pair_main_count_square_right
