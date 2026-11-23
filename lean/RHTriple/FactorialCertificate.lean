/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.FactorialCumulative
import RHTriple.HeightMajorant

/-! Remove the height smoothing and pass from interior tests to the
closed-hexagon certificate. The finite numerical bound is a premise. -/

noncomputable section
open Complex Filter Topology MeasureTheory

namespace XiPrime8845.RHTriple
open Zeta23 CertificateSmoothing

theorem zetaM3_dyadic_of_positive_test (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hcΦ : HasCompactSupport Φ)
    {η : ℝ} (hη : 0 < η) (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2-η)
    (hg : ∀ p, (planeInverse Φ p).im = 0 ∧ 0 ≤ (planeInverse Φ p).re)
    (hg0 : planeInverse Φ 0 = 1) : DyadicM3Upper (nu3F Φ).re := by
  let g (p : Plane) := (planeInverse Φ p).re
  have eg (p : Plane) : planeInverse Φ p = (g p : ℂ) :=
    Complex.ext rfl (by simpa using (hg p).1)
  have zg : g 0 = 1 := by simp [g,hg0]
  intro e he
  let a := e/(2*(1+|(nu3F Φ).re|))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨k,h,hk,hkc,hh,hhn,hh1,hmin,hmax⟩ := height_majorant_exists ha
  have hm : (∫ t, h t^3)*(nu3F Φ).re ≤ (nu3F Φ).re + e/2 := by
    have hs : 0 ≤ (∫ t, h t^3)-1 := sub_nonneg.mpr hmin
    have hc := mul_le_mul_of_nonneg_left (le_abs_self (nu3F Φ).re) hs
    have hd := mul_le_mul_of_nonneg_right
      (show (∫ t, h t^3)-1 ≤ a by linarith) (abs_nonneg (nu3F Φ).re)
    have hf : a*|(nu3F Φ).re| ≤ e/2 := by
      dsimp [a]
      rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
      nlinarith only [he]
    linarith only [hc,hd,hf]
  filter_upwards [(zetaM3_dyadic_of_height hRH hk hkc hΦ hcΦ hη hhex eg
    (fun p => (hg p).2) zg hh hhn hh1) (e/2) (by positivity)] with T hT
  exact hT.trans (mul_le_mul_of_nonneg_right (by linarith only [hm]) (Nat.cast_nonneg _))

theorem nu3Mass_eq_planeInverse_zero (Φ : Plane → ℂ) :
    nu3Mass Φ = planeInverse Φ 0 := by
  simp [nu3Mass,planeInverse,planePhase,phase]

theorem zetaM3_dyadic_of_smoothed_certificate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Integrable Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    DyadicM3Upper ((nu3F (smoothFrequency Φ e he)/nu3Mass (smoothFrequency Φ e he)).re) := by
  obtain ⟨c,cs,hex,pos,zero⟩ := smoothFrequency_admissible hΦ hcΦ hhex hg hgn hg0 he he1
  rw [nu3Mass_eq_planeInverse_zero,zero,div_one]
  exact zetaM3_dyadic_of_positive_test hRH c cs he hex pos zero

abbrev InteriorEpsilon := {e : ℝ // 0 < e ∧ e < 1}

def smoothedCertificate (Φ : Plane → ℂ) (e : InteriorEpsilon) : Plane → ℂ :=
  smoothFrequency Φ e.val e.property.1

theorem zetaM3_dyadic_of_certificate_limit (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Integrable Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {l : Filter InteriorEpsilon} [l.NeBot]
    (hlim : Tendsto (fun e => (nu3F (smoothedCertificate Φ e) /
      nu3Mass (smoothedCertificate Φ e)).re) l (𝓝 ((nu3F Φ/nu3Mass Φ).re)))
    {c : ℝ} (hc : (nu3F Φ/nu3Mass Φ).re ≤ c) : DyadicM3Upper c := by
  have H := dyadicM3Upper_of_tendsto hlim (Eventually.of_forall fun e =>
    zetaM3_dyadic_of_smoothed_certificate hRH hΦ hcΦ hhex hg hgn hg0 e.property.1 e.property.2)
  intro e he
  filter_upwards [H e he] with T hT
  exact hT.trans (mul_le_mul_of_nonneg_right (by linarith only [hc]) (Nat.cast_nonneg _))

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.zetaM3_dyadic_of_positive_test
#print axioms XiPrime8845.RHTriple.zetaM3_dyadic_of_smoothed_certificate
#print axioms XiPrime8845.RHTriple.zetaM3_dyadic_of_certificate_limit
