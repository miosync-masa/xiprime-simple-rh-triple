/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.ExplicitProduct
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! The mixed height weights created by repeated-slot deletion belong
to precisely the same admissible height class as the original test. -/

noncomputable section
open MeasureTheory
open scoped Convolution

namespace XiPrime8845.RHTriple

def heightSquareProfile (k : ℝ → ℂ) : ℝ → ℂ :=
  k ⋆[ContinuousLinearMap.mul ℂ ℂ] k

theorem heightSquareProfile_compact {k : ℝ → ℂ} (hkc : HasCompactSupport k) :
    HasCompactSupport (heightSquareProfile k) :=
  hkc.convolution (ContinuousLinearMap.mul ℂ ℂ) hkc

theorem heightSquareProfile_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) : ContDiff ℝ 2 (heightSquareProfile k) := by
  unfold heightSquareProfile
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  change ContDiff ℝ 2 (k ⋆[B] k)
  exact hkc.contDiff_convolution_right B
    ((hk.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc).locallyIntegrable)
    hk

theorem paperFT_heightSquareProfile {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (r : ℝ) :
    Zeta23.paperFT (heightSquareProfile k) r = (Zeta23.paperFT k r)^2 := by
  have hi := hk.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hkc
  rw [Zeta23.EF.paperFT_ofReal_eq_fourier, Zeta23.EF.paperFT_ofReal_eq_fourier, pow_two]
  exact Real.fourier_mul_convolution_eq hi hi _

open Zeta23 in
/-- AF's one-slot explicit formula applied twice, with independent input
profiles. Either one may be the height-square profile. Repeated labels
are still included in the resulting product of sums. -/
theorem mixed_pair_explicit_at_frequency (hRH : RiemannHypothesis)
    {k₁ k₂ : ℝ → ℂ} (h₁ : ContDiff ℝ 2 k₁) (hc₁ : HasCompactSupport k₁)
    (h₂ : ContDiff ℝ 2 k₂) (hc₂ : HasCompactSupport k₂)
    {T : ℝ} (hT : 0 < T) (b : ℝ) :
    EF.literatureRHS (shift (dilate k₁ T) b) *
        EF.literatureRHS (shift (dilate k₂ T) (-b)) =
      (∑' ρ : ZetaZero, (zetaZeroConfig.mult ρ : ℂ) *
        paperFT k₁ ((ρ : ℂ).im / (T : ℂ)) * phase ((ρ : ℂ).im*b)) *
      (∑' ρ : ZetaZero, (zetaZeroConfig.mult ρ : ℂ) *
        paperFT k₂ ((ρ : ℂ).im / (T : ℂ)) * phase ((ρ : ℂ).im*(-b))) := by
  rw [shifted_EF hRH (dilate_contDiff h₁ T) (dilate_hasCompactSupport hc₁ hT),
      shifted_EF hRH (dilate_contDiff h₂ T) (dilate_hasCompactSupport hc₂ hT)]
  unfold pairPhaseSum heightWeight
  simp_rw [paperFT_dilate _ hT]
  have hg (ρ : ZetaZero) : gammaOf (ρ : ℂ) = ((ρ : ℂ).im : ℂ) := by
    apply Complex.ext
    · simp [WeilEF.gammaOf_re]
    · simp [WeilEF.gammaOf_im, RH_implies_on_line hRH ρ.property]
  simp_rw [hg]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.heightSquareProfile_compact
#print axioms XiPrime8845.RHTriple.heightSquareProfile_contDiff
#print axioms XiPrime8845.RHTriple.paperFT_heightSquareProfile
#print axioms XiPrime8845.RHTriple.mixed_pair_explicit_at_frequency
