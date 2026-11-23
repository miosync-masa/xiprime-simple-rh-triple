/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairMain
import RHTriple.PairMarginals

/-! The three projected line tests inherit C¹ and compact support from
the plane test, and yield precisely the h²,h or h,h² pair asymptotics. -/

noncomputable section
open Complex MeasureTheory Filter Set
open scoped Convolution Asymptotics

namespace XiPrime8845.RHTriple
open Zeta23

private theorem integrate_fibre_contDiff {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F)
    (hs : ∀ t x : ℝ, F (t,x) ≠ 0 → |x| ≤ 2) :
    ContDiff ℝ 1 (fun t : ℝ => ∫ x : ℝ, F (t,x)) := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  let f : ℝ → ℂ := fun _ => 1
  let g : ℝ → ℝ → ℂ := fun t x => F (t,x)
  have h : ContDiffOn ℝ 1 (fun t : ℝ => (f ⋆[B] g t) 0) univ := by
    refine contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure ℝ)) B
      contDiffOn_const isOpen_univ (isCompact_Icc (a := (-2:ℝ)) (b := 2)) ?_
      (continuous_const.locallyIntegrable) ?_
    · intro t x _ hx
      by_contra h
      exact hx (abs_le.mp (hs t x h))
    · exact hF.contDiffOn
  rw [contDiffOn_univ] at h
  have he : (fun t : ℝ => (f ⋆[B] g t) 0) = fun t : ℝ => ∫ x : ℝ, F (t,x) := by
    funext t
    change (∫ x : ℝ, (1:ℂ)*F (t,0-x)) = _
    simpa only [one_mul,zero_sub] using
      integral_neg_eq_self (fun x : ℝ => F (t,x)) volume
  rwa [he] at h

theorem marginals_contDiff_compact {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ 1 Φ)
    {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    (ContDiff ℝ 1 (marginalX Φ) ∧ HasCompactSupport (marginalX Φ)) ∧
    (ContDiff ℝ 1 (marginalY Φ) ∧ HasCompactSupport (marginalY Φ)) ∧
    (ContDiff ℝ 1 (marginalD Φ) ∧ HasCompactSupport (marginalD Φ)) := by
  have H (t : ℝ) (ht : t ∉ Set.Icc (-1:ℝ) 1) :=
    marginals_eq_zero_of_hex hhex (t := t) (show 1-η/2 < |t| by
      have H' : 1 < |t| := lt_of_not_ge (fun h => ht (abs_le.mp h))
      linarith)
  refine ⟨⟨?_,HasCompactSupport.intro isCompact_Icc (fun t ht => (H t ht).1)⟩,
    ⟨?_,HasCompactSupport.intro isCompact_Icc (fun t ht => (H t ht).2.1)⟩,
    ⟨?_,HasCompactSupport.intro isCompact_Icc (fun t ht => (H t ht).2.2)⟩⟩
  · apply integrate_fibre_contDiff hΦ
    intro t x hx
    have hh := hhex (t,x) hx
    linarith only [hh,hη,abs_nonneg t,abs_nonneg (t+x)]
  · let F (p : ℝ × ℝ) := Φ (p.2,p.1)
    have hF : ContDiff ℝ 1 F := hΦ.comp (by fun_prop)
    apply integrate_fibre_contDiff hF
    intro t x hx
    have hh := hhex (x,t) hx
    linarith only [hh,hη,abs_nonneg t,abs_nonneg (x+t)]
  · let F (p : ℝ × ℝ) := Φ (p.2,p.1-p.2)
    have hF : ContDiff ℝ 1 F := hΦ.comp (by fun_prop)
    apply integrate_fibre_contDiff hF
    intro t x hx
    have hh := hhex (x,t-x) hx
    linarith only [hh,hη,abs_nonneg (t-x),abs_nonneg (x+(t-x))]

def collapsedPairMain (k Q : ℝ → ℂ) (T : ℝ) : ℂ :=
  pairFrequencyMain Q * (∫ r : ℝ, (paperFT k r)^3) * (Zeta23.Ncount T (2*T):ℂ)

theorem zeta_three_collapsed_pair_limits (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    ((fun T => smoothedPair (heightSquareProfile k) k (marginalD Φ) T -
      collapsedPairMain k (marginalD Φ) T) =o[atTop] (fun T => T*Real.log T)) ∧
    ((fun T => smoothedPair k (heightSquareProfile k) (marginalY Φ) T -
      collapsedPairMain k (marginalY Φ) T) =o[atTop] (fun T => T*Real.log T)) ∧
    ((fun T => smoothedPair k (heightSquareProfile k) (marginalX Φ) T -
      collapsedPairMain k (marginalX Φ) T) =o[atTop] (fun T => T*Real.log T)) := by
  obtain ⟨⟨hX,hcX⟩,⟨hY,hcY⟩,⟨hD,hcD⟩⟩ := marginals_contDiff_compact hΦ hη hhex
  let c := max (1-η/2) 0
  have hc : 0 ≤ c := le_max_right _ _
  have hc1 : c < 1 := max_lt (by linarith) zero_lt_one
  have H (t : ℝ) (ht : c < |t|) :=
    marginals_eq_zero_of_hex hhex ((le_max_left _ _).trans_lt ht)
  exact ⟨zeta_smoothed_pair_main_count_square_left hRH hk hkc hD hcD hc hc1
      (fun t h => le_of_not_gt (fun ht => h (H t ht).2.2)),
    zeta_smoothed_pair_main_count_square_right hRH hk hkc hY hcY hc hc1
      (fun t h => le_of_not_gt (fun ht => h (H t ht).2.1)),
    zeta_smoothed_pair_main_count_square_right hRH hk hkc hX hcX hc hc1
      (fun t h => le_of_not_gt (fun ht => h (H t ht).1))⟩

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.marginals_contDiff_compact
#print axioms XiPrime8845.RHTriple.zeta_three_collapsed_pair_limits
