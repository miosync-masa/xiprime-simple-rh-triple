/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairHeight
import RHTriple.PairMarginals

/-! Ordered ζ two-slot sums, with a general frequency line test. This
is the exact identity to which the two-point prime/gamma estimates apply.
It includes the diagonal with no subtraction. -/

noncomputable section
open MeasureTheory

namespace XiPrime8845.RHTriple
open Zeta23

def lineTest (Q : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t : ℝ, Q t * phase (t*x)

def smoothedPair (k₁ k₂ Q : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∑' r : ZetaZero × ZetaZero,
    heightWeight (dilate k₁ T) r.1 * heightWeight (dilate k₂ T) r.2 *
      lineTest Q (Real.log T*((r.1 : ℂ).im-(r.2 : ℂ).im))

theorem pair_phase_integral [Countable ι] {Q : ℝ → ℂ} (hQ : Integrable Q)
    {a b : ι → ℂ} (ha : Summable fun i => ‖a i‖) (hb : Summable fun j => ‖b j‖)
    (γ : ι → ℝ) (L : ℝ) :
    (∫ t : ℝ, Q t * (pairPhaseSum a γ (L*t) * pairPhaseSum b γ (-(L*t)))) =
      ∑' r : ι × ι, a r.1 * b r.2 * lineTest Q (L*(γ r.1-γ r.2)) := by
  let F (r : ι × ι) (t : ℝ) := (a r.1*b r.2) * (Q t * phase (t*(L*(γ r.1-γ r.2))))
  have hI (r : ι × ι) : Integrable (F r) :=
    (hQ.mul_bdd (c := 1) ((continuous_phase.comp (continuous_id.mul
      continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _ => (norm_phase _).le)).const_mul _
  have hmajor : Summable fun r : ι × ι => ∫ t, ‖F r t‖ := by
    have he (r : ι × ι) : (∫ t, ‖F r t‖) = ‖a r.1‖*‖b r.2‖*(∫ t, ‖Q t‖) := by
      simp only [F, norm_mul, norm_phase, mul_one, integral_const_mul]
    simp_rw [he]
    simpa only [norm_mul] using (ha.mul_norm hb).mul_right (∫ t, ‖Q t‖)
  have hInt (r : ι × ι) : (∫ t, F r t) =
      a r.1*b r.2*lineTest Q (L*(γ r.1-γ r.2)) := by
    rw [lineTest, ← integral_const_mul]
  simp_rw [← hInt]
  rw [integral_tsum_of_summable_integral_norm hI hmajor]
  apply integral_congr_ae
  filter_upwards [] with t
  have hA : Summable fun i => ‖a i * phase (γ i * (L*t))‖ := by
    simpa only [norm_mul, norm_phase, mul_one] using ha
  have hB : Summable fun i => ‖b i * phase (γ i * -(L*t))‖ := by
    simpa only [norm_mul, norm_phase, mul_one] using hb
  unfold pairPhaseSum
  rw [tsum_mul_tsum_of_summable_norm hA hB, ← tsum_mul_left]
  congr 1
  ext r
  have hp : phase (γ r.1*(L*t)) * phase (γ r.2* -(L*t)) =
      phase (t*(L*(γ r.1-γ r.2))) := by
    unfold phase
    rw [← Complex.exp_add]
    push_cast
    congr 1
    ring
  unfold F
  rw [← hp]
  ring

private theorem zetaZero_countable_for_pairs : Countable ZetaZero := by
  apply Set.countable_coe_iff.mpr
  have heq : zetaZeroConfig.carrier = ⋃ n : ℕ, zetaZeroConfig.window (-(n : ℝ)) n := by
    ext ρ
    simp only [Set.mem_iUnion, ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hρ
      obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
      exact ⟨n, hρ, by linarith [neg_abs_le ρ.im], (le_abs_self _).trans hn.le⟩
    · rintro ⟨n, hρ, _, _⟩
      exact hρ
  rw [heq]
  exact Set.countable_iUnion fun n => (zetaZeroConfig.window_finite _ _).countable

theorem smoothedPair_eq_integral_EF (hRH : RiemannHypothesis)
    {k₁ k₂ Q : ℝ → ℂ} (h₁ : ContDiff ℝ 2 k₁) (hc₁ : HasCompactSupport k₁)
    (h₂ : ContDiff ℝ 2 k₂) (hc₂ : HasCompactSupport k₂) (hQ : Integrable Q)
    {T : ℝ} (hT : 0 < T) :
    smoothedPair k₁ k₂ Q T =
      ∫ t : ℝ, Q t * (EF.literatureRHS (shift (dilate k₁ T) (Real.log T*t)) *
        EF.literatureRHS (shift (dilate k₂ T) (-(Real.log T*t)))) := by
  let : Countable ZetaZero := zetaZero_countable_for_pairs
  simp_rw [shifted_EF hRH (dilate_contDiff h₁ T) (dilate_hasCompactSupport hc₁ hT),
    shifted_EF hRH (dilate_contDiff h₂ T) (dilate_hasCompactSupport hc₂ hT)]
  exact (pair_phase_integral hQ
    (heightWeight_summable_norm (dilate_contDiff h₁ T) (dilate_hasCompactSupport hc₁ hT))
    (heightWeight_summable_norm (dilate_contDiff h₂ T) (dilate_hasCompactSupport hc₂ hT))
    (fun ρ => (ρ : ℂ).im) (Real.log T)).symm

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.pair_phase_integral
#print axioms XiPrime8845.RHTriple.smoothedPair_eq_integral_EF
