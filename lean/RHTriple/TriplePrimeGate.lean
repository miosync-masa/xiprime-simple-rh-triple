/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.TriplePrimeDiagonal
import RHTriple.TriplePrimeSymmetry
import RHTriple.PolarGate

/-! The two same-sign terms vanish because their positive signed logs
cannot add to zero. Of the six mixed terms, the three with two plus
signs are permutations of (+,+,-); simultaneous reflection reduces
the other three to those. These are changes of variables of the actual
integral, not assumptions of symmetric tests or even profiles. -/

noncomputable section
open Complex MeasureTheory Filter Finset
open scoped Asymptotics

namespace XiPrime8845.RHTriple

private def HexTest (η : ℝ) (Φ : ℝ × ℝ → ℂ) : Prop :=
  ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η

private theorem hexTest_swap01 {Φ : ℝ × ℝ → ℂ} {η : ℝ} (h : HexTest η Φ) :
    HexTest η (Φ ∘ swap01) := by
  intro x hx
  have hh := h (swap01 x) hx
  change |x.2|+|x.1|+|x.2+x.1| ≤ _ at hh
  simpa only [add_comm x.2 x.1, add_comm |x.2| |x.1|] using hh

private theorem hexTest_swap12 {Φ : ℝ × ℝ → ℂ} {η : ℝ} (h : HexTest η Φ) :
    HexTest η (Φ ∘ swap12) := by
  intro x hx
  have hh := h (swap12 x) hx
  change |x.1|+|-(x.1+x.2)|+|x.1+ -(x.1+x.2)| ≤ _ at hh
  rw [show x.1+ -(x.1+x.2) = -x.2 by ring, abs_neg, abs_neg] at hh
  linarith only [hh]

private theorem hexTest_reflect {Φ : ℝ × ℝ → ℂ} {η : ℝ} (h : HexTest η Φ) :
    HexTest η (Φ ∘ reflect01) := by
  intro x hx
  have hh := h (reflect01 x) hx
  change |-x.1|+|-x.2|+|-x.1+-x.2| ≤ _ at hh
  simpa only [← neg_add, abs_neg] using hh

private theorem signedTriple_twoPlus_or_more {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : HexTest η Φ) (N : ℝ → ℕ) (s t u : Bool)
    (h : (s = true ∧ t = true) ∨ (s = true ∧ u = true) ∨ (t = true ∧ u = true)) :
    (fun T => signedTripleIntegral k Φ (N T) T s t u) =o[atTop] (fun T => T*Real.log T) := by
  have P {Ψ : ℝ × ℝ → ℂ} (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (hH : HexTest η Ψ) :=
    signedTriple_ppm_isLittleO hk hkc hΨ hΨc hη hH N
  have H12 := hΦ.comp swap12.continuous
  have H12c := hΦc.comp_homeomorph swap12
  have H01 := hΦ.comp swap01.continuous
  have H01c := hΦc.comp_homeomorph swap01
  cases s <;> cases t <;> cases u <;> simp at h
  · refine (P (H01.comp swap12.continuous) (H01c.comp_homeomorph swap12)
      (hexTest_swap12 (hexTest_swap01 hhex))).congr_left ?_
    intro T
    exact ((signedTriple_swap01 k Φ (N T) T false true true).trans
      (signedTriple_swap12 hk H01 H01c (N T) T true false true)).symm
  · exact (P H12 H12c (hexTest_swap12 hhex)).congr_left fun T =>
      (signedTriple_swap12 hk hΦ hΦc (N T) T true false true).symm
  · exact P hΦ hΦc hhex
  · have he : (fun T => signedTripleIntegral k Φ (N T) T true true true) =ᶠ[atTop]
        (fun _ => (0:ℂ)) := signedTriple_ppp_eventually_zero hk hkc hΦ hΦc hη hhex N
    exact (Asymptotics.isLittleO_zero _ _).congr' he.symm Filter.EventuallyEq.rfl

theorem signedTriple_any_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η)
    (N : ℝ → ℕ) (s t u : Bool) :
    (fun T => signedTripleIntegral k Φ (N T) T s t u) =o[atTop] (fun T => T*Real.log T) := by
  by_cases h : (s = true ∧ t = true) ∨ (s = true ∧ u = true) ∨ (t = true ∧ u = true)
  · exact signedTriple_twoPlus_or_more hk hkc hΦ hΦc hη hhex N s t u h
  · have hh : ((!s) = true ∧ (!t) = true) ∨ ((!s) = true ∧ (!u) = true) ∨ ((!t) = true ∧ (!u) = true) := by
      cases s <;> cases t <;> cases u <;> simp_all
    refine (signedTriple_twoPlus_or_more (hk.comp reflectHeight.continuous)
      (hkc.comp_homeomorph reflectHeight) (hΦ.comp reflect01.continuous)
      (hΦc.comp_homeomorph reflect01) hη (hexTest_reflect hhex) N (!s) (!t) (!u) hh).congr_left ?_
    exact fun T => (signedTriple_flip hk hΦ hΦc (N T) T s t u).symm

theorem triplePrimeEF_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) (p : ℝ) :
    (fun T => mixedEFIntegral k Φ p T 1 1 1) =o[atTop] (fun T => T*Real.log T) := by
  have H := Asymptotics.IsLittleO.fun_sum (s := (univ : Finset Bool)) (fun s _ =>
    Asymptotics.IsLittleO.fun_sum (s := (univ : Finset Bool)) (fun t _ =>
      Asymptotics.IsLittleO.fun_sum (s := (univ : Finset Bool)) (fun u _ =>
        signedTriple_any_isLittleO hk hkc hΦ hΦc hη hhex (fun T => ⌊T^p⌋₊) s t u)))
  refine H.neg_left.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  exact (triplePrimeEF_eq_eight_signs hk hΦ hΦc p hT).symm

/-- Only the actual all-gamma integral and the three paired-prime layouts
survive at order `T log T`. This still precedes evaluating their limits. -/
theorem smoothedTriple_sub_gamma_and_pairs_isLittleO (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    let d := 1-η/4
    (fun T => smoothedTriple k Φ T -
      (mixedEFIntegral k Φ d T 2 2 2 + retainedPrimePairs k Φ d T))
      =o[atTop] (fun T => T*Real.log T) := by
  let d := 1-η/4
  have H := smoothedTriple_sub_survivors_isLittleO hRH hk hkc hΦ hΦc hη hη1 hhex
  have H' := triplePrimeEF_isLittleO hk.continuous hkc hΦ hΦc hη hhex d
  refine (H.add H').congr_left ?_
  intro T
  change smoothedTriple k Φ T - (_ + mixedEFIntegral k Φ d T 1 1 1 + _) +
    mixedEFIntegral k Φ d T 1 1 1 = _
  abel

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.signedTriple_any_isLittleO
#print axioms XiPrime8845.RHTriple.triplePrimeEF_isLittleO
#print axioms XiPrime8845.RHTriple.smoothedTriple_sub_gamma_and_pairs_isLittleO
