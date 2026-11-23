/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.CertificateSmoothing

/-! Fourier inversion identities for the regularized certificate.
The normalization of the inverse is Lebesgue measure and the positive
phase 2πi·dot; it is the inverse associated with the triple test. -/

noncomputable section
open MeasureTheory Complex Filter
open scoped Convolution

namespace XiPrime8845.RHTriple.CertificateSmoothing

def planePhase (x p : Plane) : ℂ :=
  phase (2*Real.pi*(x.1*p.1+x.2*p.2))

def planeInverse (Φ : Plane → ℂ) (x : Plane) : ℂ :=
  ∫ p : Plane, Φ p * planePhase x p

@[simp] theorem norm_planePhase (x p : Plane) : ‖planePhase x p‖ = 1 :=
  norm_phase _

private theorem continuous_planePhase (x : Plane) : Continuous (planePhase x) := by
  unfold planePhase
  exact continuous_phase.comp (by fun_prop)

theorem planeInverse_triple_coordinates (Φ : Plane → ℂ) (L a b c : ℝ) :
    planeInverse Φ (L/(2*Real.pi)*(a-c), L/(2*Real.pi)*(b-c)) =
      ∫ p : Plane, Φ p * phase (differences L a b c p) := by
  apply integral_congr_ae
  filter_upwards [] with p
  unfold planePhase differences
  congr 2
  field_simp [Real.pi_ne_zero]

private theorem planePhase_add (x p q : Plane) :
    planePhase x (p+q) = planePhase x p * planePhase x q := by
  unfold planePhase phase
  rw [← exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

private theorem planePhase_smul (a : ℝ) (x p : Plane) :
    planePhase (a • x) p = planePhase x (a • p) := by
  unfold planePhase
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  congr 1
  ring

private theorem planePhase_rev (x p : Plane) :
    star (planePhase x p) = planePhase x (-p) := by
  unfold planePhase phase
  rw [show star (exp _) = exp (star (I * (↑(2 * Real.pi * (x.1 * p.1 + x.2 * p.2))))) by
    exact (exp_conj _).symm]
  congr 1
  simp only [star_mul, star_def, conj_I, conj_ofReal, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

private theorem planeInverse_convolution {f g : Plane → ℂ} (hf : Integrable f)
    (hg : Integrable g) (x : Plane) :
    planeInverse (planeConvolution f g) x = planeInverse f x * planeInverse g x := by
  let F (p q : Plane) := (f q * g (p-q)) * planePhase x p
  have hI : Integrable (fun z : Plane × Plane => F z.1 z.2) (volume.prod volume) := by
    have hbase := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hg
    have hphase : Continuous (fun z : Plane × Plane => planePhase x z.1) :=
      (continuous_planePhase x).comp continuous_fst
    exact hbase.mul_bdd (c := 1) hphase.aestronglyMeasurable
      (Eventually.of_forall fun _ => (norm_planePhase _ _).le)
  have hInner (q : Plane) : (∫ p, F p q) = (f q * planePhase x q) * planeInverse g x := by
    rw [← integral_add_right_eq_self (fun p : Plane => F p q) q, planeInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    unfold F
    rw [add_sub_cancel_right, planePhase_add]
    ring
  calc
    _ = ∫ p, ∫ q, F p q := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold planeConvolution
      rw [convolution, ← integral_mul_const]
      rfl
    _ = ∫ q, ∫ p, F p q := integral_integral_swap hI
    _ = _ := by
      simp_rw [hInner, integral_mul_const]
      rfl

/-- The positive inverse of the autocorrelation used by the GdLL
certificate. The input itself need not be continuous or nonnegative. -/
theorem planeInverse_real_autocorrelation {f : Plane → ℝ} (hf : Integrable f) (x : Plane) :
    planeInverse (fun t => ((∫ q, f q * f (q-t) : ℝ) : ℂ)) x =
      (‖planeInverse (fun q => (f q : ℂ)) x‖^2 : ℝ) := by
  let F (q : Plane) : ℂ := f q
  let R (q : Plane) : ℂ := f (-q)
  have iF : Integrable F := Complex.ofRealCLM.integrable_comp hf
  have iR : Integrable R := iF.comp_neg
  have hconv : (fun t => ((∫ q, f q * f (q-t) : ℝ) : ℂ)) = planeConvolution F R := by
    funext t
    unfold planeConvolution
    rw [convolution_def, ← integral_complex_ofReal]
    simp only [ContinuousLinearMap.mul_apply', F, R, neg_sub, ofReal_mul]
  have hconj : planeInverse R x = star (planeInverse F x) := by
    unfold planeInverse
    rw [star_def, ← integral_conj, ← integral_neg_eq_self (fun p => R p * planePhase x p) volume]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [map_mul]
    change R (-p) * planePhase x (-p) = star (F p) * star (planePhase x p)
    rw [planePhase_rev]
    simp [F,R]
  rw [hconv, planeInverse_convolution iF iR, hconj, star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

theorem planeInverse_contract (Φ : Plane → ℂ) {a : ℝ} (ha : 0 < a) (x : Plane) :
    planeInverse (contract Φ a) x = planeInverse Φ (a • x) := by
  let F (p : Plane) := Φ p * planePhase (a • x) p
  have he (p : Plane) : contract Φ a p * planePhase x p =
      ((a:ℂ)^2)⁻¹ * F (a⁻¹ • p) := by
    unfold contract F
    rw [planePhase_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, mul_assoc]
  unfold planeInverse
  simp_rw [he, integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume F ha.le]
  rw [show Module.finrank ℝ Plane = 2 by simp [Plane, Module.finrank_prod]]
  rw [Complex.real_smul, Complex.ofReal_pow, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact pow_ne_zero 2 (ofReal_ne_zero.mpr ha.ne')

theorem mollifier_integral (ε : ℝ) (hε : 0 < ε) : (∫ p, mollifier ε hε p) = 1 := by
  unfold mollifier
  rw [integral_complex_ofReal, ContDiffBump.integral_normed, ofReal_one]

theorem mollifier_integrable (ε : ℝ) (hε : 0 < ε) :
    Integrable (mollifier ε hε) :=
  (mollifier_contDiff ε hε (n := 1)).continuous.integrable_of_hasCompactSupport
    (mollifier_compact ε hε)

/-- The squared Fourier multiplier is at most one pointwise. This bound is
independent of the certificate or the sharpness of its band edge. -/
theorem mollifierInverse_norm_le_one (ε : ℝ) (hε : 0 < ε) (x : Plane) :
    ‖planeInverse (mollifier ε hε) x‖ ≤ 1 := by
  apply (norm_integral_le_integral_norm _).trans
  simp only [norm_mul, norm_planePhase, mul_one]
  simpa only [mollifier, Complex.norm_real,
    Real.norm_of_nonneg ((mollifierSeed ε hε).nonneg_normed _)] using
    (mollifierSeed ε hε).integral_normed (μ := (volume : Measure Plane)).le

private theorem mollifier_inv_real (ε : ℝ) (hε : 0 < ε) (x : Plane) :
    star (planeInverse (mollifier ε hε) x) = planeInverse (mollifier ε hε) x := by
  unfold planeInverse
  rw [star_def, ← integral_conj]
  rw [← integral_neg_eq_self (fun p : Plane => mollifier ε hε p * planePhase x p) volume]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [map_mul]
  change star (mollifier ε hε p) * star (planePhase x p) = _
  rw [planePhase_rev]
  simp [mollifier, ContDiffBump.normed_neg]

theorem planeInverse_smoothFrequency {Φ : Plane → ℂ} (hΦ : Integrable Φ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (x : Plane) :
    planeInverse (smoothFrequency Φ ε hε) x =
      planeInverse Φ ((1-ε) • x) * (‖planeInverse (mollifier ε hε) x‖^2 : ℝ) := by
  have ha : 0 < 1-ε := by linarith
  have hia : Integrable (contract Φ (1-ε)) := (hΦ.comp_smul (inv_ne_zero ha.ne')).const_mul _
  have hφ := mollifier_integrable ε hε
  have hcψ : HasCompactSupport (smoothingKernel ε hε) :=
    (mollifier_compact ε hε).convolution (ContinuousLinearMap.mul ℝ ℂ) (mollifier_compact ε hε)
  have hψ : ContDiff ℝ 1 (smoothingKernel ε hε) :=
    (mollifier_compact ε hε).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      hφ.locallyIntegrable (mollifier_contDiff ε hε)
  rw [smoothFrequency, planeInverse_convolution hia
    (hψ.continuous.integrable_of_hasCompactSupport hcψ), planeInverse_contract Φ ha,
    smoothingKernel, planeInverse_convolution hφ hφ]
  let z := planeInverse (mollifier ε hε) x
  congr 1
  change z*z = (‖z‖^2 : ℝ)
  calc
    z*z = z*star z := congrArg (fun w => z*w) (mollifier_inv_real ε hε x).symm
    _ = _ := by rw [star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem smoothFrequency_admissible {Φ : Plane → ℂ} (hΦ : Integrable Φ)
    (hcΦ : HasCompactSupport Φ) (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p : ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    let Ψ := smoothFrequency Φ ε hε
    ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ ∧
      (∀ p, Ψ p ≠ 0 → hexGauge p ≤ 2-ε) ∧
      (∀ p, (planeInverse Ψ p).im = 0 ∧ 0 ≤ (planeInverse Ψ p).re) ∧
      planeInverse Ψ 0 = 1 := by
  have H := smoothFrequency_regular hΦ hcΦ hε hε1 (n := 1)
  refine ⟨H.1,H.2,smoothFrequency_margin hhex hε hε1,?_,?_⟩
  · intro p
    rw [planeInverse_smoothFrequency hΦ hε hε1, hg, ← ofReal_mul]
    exact ⟨ofReal_im _, by simpa only [ofReal_re] using mul_nonneg (hgn _) (sq_nonneg _)⟩
  · rw [planeInverse_smoothFrequency hΦ hε hε1, smul_zero, hg, hg0]
    have H0 : planeInverse (mollifier ε hε) 0 = 1 := by
      simpa [planeInverse, planePhase, phase] using mollifier_integral ε hε
    simp [H0]

end XiPrime8845.RHTriple.CertificateSmoothing

#print axioms XiPrime8845.RHTriple.CertificateSmoothing.planeInverse_smoothFrequency
#print axioms XiPrime8845.RHTriple.CertificateSmoothing.planeInverse_real_autocorrelation
#print axioms XiPrime8845.RHTriple.CertificateSmoothing.smoothFrequency_admissible
#print axioms XiPrime8845.RHTriple.CertificateSmoothing.planeInverse_triple_coordinates
#print axioms XiPrime8845.RHTriple.CertificateSmoothing.mollifierInverse_norm_le_one
