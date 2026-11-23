/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.TriplePrimeGate
import RHTriple.PairedLimit
import RHTriple.HeightMass
import RHTriple.ZetaScale

/-! The smoothed ordered three-slot asymptotic for ζ, with all the
analytic estimates proved and RH passed explicitly to the zero side. -/

noncomputable section
open Complex MeasureTheory Filter Topology
open scoped Asymptotics

namespace XiPrime8845.RHTriple

def pairLines (Φ : ℝ × ℝ → ℂ) : ℂ := pairLine Φ false + pairLine Φ true

/-- The sign-summed pair traces on `(u,-u)`, `(u,0)`, and `(0,u)`,
plus the value at the origin. The pullbacks keep both orientations. -/
def tripleFrequencyMain (Φ : ℝ × ℝ → ℂ) : ℂ :=
  Φ (0,0) + (pairLines Φ + pairLines (Φ ∘ swap12) + pairLines ((Φ ∘ swap01) ∘ swap12))

private theorem pairedMain_normalized_tendsto {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    Tendsto (fun T => pairedMain k Φ (1-η/4) T / ((T*Real.log T : ℝ):ℂ)) atTop
      (𝓝 (pairLines Φ * heightTripleMass k)) := by
  simpa only [pairedMain, add_div, pairLines, add_mul] using
    (pairedPrimeDiagonal_normalized_tendsto hk hkc hΦ hΦc hη hη1 hhex false).add
      (pairedPrimeDiagonal_normalized_tendsto hk hkc hΦ hΦc hη hη1 hhex true)

theorem retainedPrimePairs_normalized_tendsto {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    Tendsto (fun T => retainedPrimePairs k Φ (1-η/4) T / ((T*Real.log T : ℝ):ℂ)) atTop
      (𝓝 ((pairLines Φ + pairLines (Φ ∘ swap12) + pairLines ((Φ ∘ swap01) ∘ swap12)) *
        heightTripleMass k)) := by
  have H01 : ContDiff ℝ 1 (swap01 : ℝ × ℝ → ℝ × ℝ) := by
    change ContDiff ℝ 1 (fun x : ℝ × ℝ => (x.2,x.1))
    fun_prop
  have H12 : ContDiff ℝ 1 (swap12 : ℝ × ℝ → ℝ × ℝ) := by
    change ContDiff ℝ 1 (fun x : ℝ × ℝ => (x.1,-(x.1+x.2)))
    fun_prop
  have h₁ {Ψ : ℝ × ℝ → ℂ}
      (h : ∀ x : ℝ × ℝ, Ψ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
      ∀ x : ℝ × ℝ, (Ψ ∘ swap01) x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η := by
    intro x hx
    have hh := h (swap01 x) hx
    change |x.2|+|x.1|+|x.2+x.1| ≤ _ at hh
    simpa only [add_comm x.2 x.1, add_comm |x.2| |x.1|] using hh
  have h₂ {Ψ : ℝ × ℝ → ℂ}
      (h : ∀ x : ℝ × ℝ, Ψ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
      ∀ x : ℝ × ℝ, (Ψ ∘ swap12) x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η := by
    intro x hx
    have hh := h (swap12 x) hx
    change |x.1|+|-(x.1+x.2)|+|x.1+ -(x.1+x.2)| ≤ _ at hh
    rw [show x.1+ -(x.1+x.2) = -x.2 by ring, abs_neg, abs_neg] at hh
    linarith only [hh]
  have A := pairedMain_normalized_tendsto hk hkc hΦ hΦc hη hη1 hhex
  have B := pairedMain_normalized_tendsto hk hkc (hΦ.comp H12)
    (hΦc.comp_homeomorph swap12) hη hη1 (h₂ hhex)
  have C := pairedMain_normalized_tendsto hk hkc ((hΦ.comp H01).comp H12)
    ((hΦc.comp_homeomorph swap01).comp_homeomorph swap12) hη hη1 (h₂ (h₁ hhex))
  simpa only [retainedPrimePairs, add_div, add_mul] using (A.add B).add C

private theorem isLittleO_from_normalized {F : ℝ → ℂ} {a : ℂ}
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

private theorem zeta_smoothed_triple_main_of_small_margin (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    (fun T => smoothedTriple k Φ T -
      tripleFrequencyMain Φ * (∫ r : ℝ, (Zeta23.paperFT k r)^3) * (zetaMainScale T : ℂ))
      =o[atTop] (fun T => T*Real.log T) := by
  let d := 1-η/4
  let F (T : ℝ) := mixedEFIntegral k Φ d T 2 2 2 + retainedPrimePairs k Φ d T
  have h₁ := allGamma_normalized_tendsto hk hkc hΦ.continuous hΦc d
  have h₂ := retainedPrimePairs_normalized_tendsto hk hkc hΦ hΦc hη hη1 hhex
  have H : Tendsto (fun T => F T / ((T*Real.log T : ℝ):ℂ)) atTop
      (𝓝 (tripleFrequencyMain Φ * heightTripleMass k)) := by
    simpa only [F, add_div, tripleFrequencyMain, add_mul] using h₁.add h₂
  have hG := isLittleO_from_normalized H
  have hZero := smoothedTriple_sub_gamma_and_pairs_isLittleO hRH hk hkc hΦ.continuous hΦc hη hη1 hhex
  refine (hZero.add hG).congr_left ?_
  intro T
  change smoothedTriple k Φ T - F T +
    (F T - tripleFrequencyMain Φ * heightTripleMass k * ((T*Real.log T : ℝ):ℂ)) = _
  rw [← heightTripleMass_eq_height_integral hk hkc]
  unfold zetaMainScale
  push_cast
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The only assumptions are explicit RH and the regularity and strict
support of the height/frequency test. Repeated zero slots are included. -/
theorem zeta_smoothed_triple_main (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    (fun T => smoothedTriple k Φ T -
      tripleFrequencyMain Φ * (∫ r : ℝ, (Zeta23.paperFT k r)^3) * (zetaMainScale T : ℂ))
      =o[atTop] (fun T => T*Real.log T) :=
  zeta_smoothed_triple_main_of_small_margin hRH hk hkc hΦ hΦc
    (lt_min hη zero_lt_one) (min_le_right _ _) (fun x hx =>
      (hhex x hx).trans (sub_le_sub_left (min_le_left _ _) _))

theorem zeta_smoothed_triple_main_count (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    (fun T => smoothedTriple k Φ T -
      tripleFrequencyMain Φ * (∫ r : ℝ, (Zeta23.paperFT k r)^3) * (Zeta23.Ncount T (2*T):ℂ))
      =o[atTop] (fun T => T*Real.log T) := by
  let a := tripleFrequencyMain Φ * (∫ r : ℝ, (Zeta23.paperFT k r)^3)
  have H := zeta_smoothed_triple_main hRH hk hkc hΦ hΦc hη hhex
  have hcount := zetaDyadicCount_sub_scale_isLittleO.const_mul_left a
  refine (H.sub hcount).congr_left fun T => ?_
  change smoothedTriple k Φ T - a * (zetaMainScale T : ℂ) -
    a*((Zeta23.Ncount T (2*T):ℂ) - (zetaMainScale T : ℂ)) = _
  ring

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.retainedPrimePairs_normalized_tendsto
#print axioms XiPrime8845.RHTriple.zeta_smoothed_triple_main
#print axioms XiPrime8845.RHTriple.zeta_smoothed_triple_main_count
