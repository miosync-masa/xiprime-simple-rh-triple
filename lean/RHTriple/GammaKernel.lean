/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.ExplicitProduct

/-! The ζ archimedean kernel in Rudnick–Sarnak (3.15), in AF normalization.
The parameter here is the Fourier variable *after* multiplication by `T`.
The real digamma series provides a contour-free route to the Fourier tail. -/

noncomputable section
open Complex MeasureTheory Filter

namespace XiPrime8845.RHTriple
open Zeta23

/-- The ζ instance of the kernel `g_T(x)` of Rudnick–Sarnak (3.15). -/
def scaledGamma (k : ℝ → ℂ) (T x : ℝ) : ℂ :=
  ∫ r : ℝ, (paperFT k r * (mu (T * r) : ℂ)) * phase (-(r * x))

theorem gammaFactor_dilate (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (b : ℝ) :
    gammaFactor (dilate k T) b = (T : ℂ) * scaledGamma k T (-(T*b)) := by
  let F : ℝ → ℂ := fun r => paperFT (dilate k T) r * (mu r : ℂ) * phase (r*b)
  change (∫ r, F r) = _
  have he (r : ℝ) : F (T*r) =
      paperFT k r * (mu (T*r) : ℂ) * phase (-(r * -(T*b))) := by
    dsimp [F]
    rw [paperFT_dilate k hT, Complex.ofReal_mul, mul_comm (T:ℂ), mul_div_cancel_right₀ _
      (show (T:ℂ) ≠ 0 by exact_mod_cast hT.ne')]
    congr 1
    ring
  have h := Measure.integral_comp_mul_left F T
  simp_rw [he] at h
  rw [abs_inv, abs_of_pos hT, Complex.real_smul, Complex.ofReal_inv] at h
  unfold scaledGamma
  rw [h, ← mul_assoc, mul_inv_cancel₀ (show (T:ℂ) ≠ 0 by exact_mod_cast hT.ne'), one_mul]

theorem mu_log_bound : ∃ C : ℝ, 0 < C ∧ ∀ r, |mu r| ≤ C * Real.log (2 + |r|) := by
  obtain ⟨C, hC, hΓ⟩ := WeilEF.norm_logDeriv_Gammaℝ_le
  refine ⟨2*C / (2 * Real.pi), by positivity, fun r => ?_⟩
  have hzero : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsym := WeilEF.gammaR_bracket r
  have hcast : (mu r : ℂ) = (1/(2*Real.pi) : ℂ) *
      (logDeriv Complex.Gammaℝ (1/2 + (r : ℂ)*I) + logDeriv Complex.Gammaℝ (1/2 - (r : ℂ)*I)) := by
    rw [hsym]
    unfold mu
    have hre : (1/4 : ℂ) + (r : ℂ)/2*I = 1/4 + I*r/2 := by ring
    rw [hre]
    push_cast
    ring
  have hpos := hΓ (1/2) r le_rfl (by norm_num)
  have hneg := hΓ (1/2) (-r) le_rfl (by norm_num)
  rw [abs_neg] at hneg
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hcast, norm_mul]
  have hf : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hf]
  have hsum := norm_add_le (logDeriv Complex.Gammaℝ (1/2 + (r : ℂ)*I))
    (logDeriv Complex.Gammaℝ (1/2 - (r : ℂ)*I))
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hpos hneg
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2*C * Real.log (2+|r|)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

theorem paperFT_log_integrable {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Integrable (fun r : ℝ => ‖paperFT k r‖ * Real.log (2+|r|)) := by
  obtain ⟨R, hR⟩ := EF.exists_abs_le_of_hasCompactSupport hkc
  let A := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖
  have hA : 0 ≤ A := by positivity
  have hF := (EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hk hkc))
  have hlog : Continuous (fun r : ℝ => Real.log (2+|r|)) :=
    (continuous_const.add continuous_abs).log (fun r => (show 0 < 2+|r| by linarith [abs_nonneg r]).ne')
  refine ((integrable_one_add_norm (E := ℝ) (r := 3/2) (by norm_num)).const_mul (6*A)).mono'
    (hF.norm.aestronglyMeasurable.mul hlog.aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
  have hn := EF.norm_paperFT_mul_one_add_sq_le hk hR r
  have hL : 0 ≤ Real.log (2+|r|) := Real.log_nonneg (by linarith [abs_nonneg r])
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hL), Real.norm_eq_abs]
  calc
    _ ≤ (A/(1+r^2)) * Real.log (2+|r|) :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ (by positivity)).2 hn) hL
    _ = A * (Real.log (2+|r|)/(1+|r|^2)) := by rw [sq_abs]; ring
    _ ≤ A * (6 * (1+|r|)^(-(3/2):ℝ)) :=
      mul_le_mul_of_nonneg_left (WeilEF.log_two_add_div_le (abs_nonneg r)) hA
    _ = _ := by ring

theorem scaledGamma_uniform_log {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ≥ 1, ∀ x, ‖scaledGamma k T x‖ ≤ C * (1 + Real.log T) := by
  obtain ⟨C, hC, hμ⟩ := mu_log_bound
  let A : ℝ := ∫ r : ℝ, ‖paperFT k r‖
  let B : ℝ := ∫ r : ℝ, ‖paperFT k r‖ * Real.log (2 + |r|)
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun r => mul_nonneg (norm_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg r])))
  have hF := EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hk hkc)
  refine ⟨C*(A+B), by positivity, ?_⟩
  intro T hT x
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hdom : Integrable (fun r : ℝ => C * (Real.log T * ‖paperFT k r‖ +
      ‖paperFT k r‖ * Real.log (2+|r|))) :=
    ((hF.norm.const_mul _).add (paperFT_log_integrable hk hkc)).const_mul _
  have hmeas : AEStronglyMeasurable (fun r : ℝ => paperFT k r * (mu (T*r) : ℂ) *
      phase (-(r*x))) := hF.aestronglyMeasurable.mul
    ((Complex.continuous_ofReal.comp (gammaFacts.smooth.continuous.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) |>.mul
    (continuous_phase.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable
  have hpt (r : ℝ) : ‖paperFT k r * (mu (T*r) : ℂ) * phase (-(r*x))‖ ≤
      C * (Real.log T * ‖paperFT k r‖ + ‖paperFT k r‖ * Real.log (2+|r|)) := by
    have hR : 0 < 2 + |r| := by linarith [abs_nonneg r]
    have hl : Real.log (2+|T*r|) ≤ Real.log T + Real.log (2+|r|) := by
      rw [← Real.log_mul hT0.ne' hR.ne', abs_mul, abs_of_pos hT0]
      exact Real.log_le_log (by positivity) (by nlinarith)
    rw [norm_mul, norm_phase, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖paperFT k r‖ * (C * (Real.log T + Real.log (2+|r|))) :=
        mul_le_mul_of_nonneg_left ((hμ _).trans (mul_le_mul_of_nonneg_left hl hC.le)) (norm_nonneg _)
      _ = _ := by ring
  have hi := hdom.mono' hmeas (Eventually.of_forall hpt)
  unfold scaledGamma
  calc
    _ ≤ ∫ r : ℝ, ‖paperFT k r * (mu (T*r) : ℂ) * phase (-(r*x))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r : ℝ, C * (Real.log T * ‖paperFT k r‖ + ‖paperFT k r‖ * Real.log (2+|r|)) :=
      integral_mono hi.norm hdom hpt
    _ = C * (Real.log T * A + B) := by
      rw [integral_const_mul, integral_add (hF.norm.const_mul _) (paperFT_log_integrable hk hkc), integral_const_mul]
    _ ≤ C*(A+B)*(1+Real.log T) := by
      nlinarith [mul_nonneg hC.le hA, mul_nonneg hC.le (mul_nonneg hB hlog)]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.gammaFactor_dilate
#print axioms XiPrime8845.RHTriple.scaledGamma_uniform_log
