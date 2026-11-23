/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTripleIntegration.CertificateBound
import RHTriple.CertificateApproximation
import TripleCorrelation.Nu3Continuity

/-! Three-branch endgame. The normalized Fourier limit follows from the
actual positive smoothing family and the certificate branch's continuity
theorem. Only witness properties and its numerical gate remain inputs. -/

noncomputable section
open Complex Filter Topology MeasureTheory
open XiPrime8845.RHTriple XiPrime8845.RHTriple.CertificateSmoothing

namespace XiPrime8845.RHTripleIntegration
open Zeta23

private def eps (n : ℕ) : InteriorEpsilon :=
  ⟨((n:ℝ)+2)⁻¹, inv_pos.mpr (by positivity), by
    rw [← one_div,div_lt_iff₀ (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]⟩

private theorem eps_small (n : ℕ) : (eps n).val ≤ 1/2 := by
  change ((n:ℝ)+2)⁻¹ ≤ 1/2
  rw [← one_div,div_le_iff₀ (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem eps_tendsto : Tendsto (fun n => (eps n).val) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (2:ℝ)
    tendsto_natCast_atTop_atTop)

theorem normalized_smoothedCertificate_tendsto {Φ : Plane → ℂ}
    (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2) (hm : nu3Mass Φ ≠ 0) :
    Tendsto (fun e => (nu3F (smoothedCertificate Φ e) /
      nu3Mass (smoothedCertificate Φ e)).re) (Filter.map eps atTop)
      (𝓝 ((nu3F Φ/nu3Mass Φ).re)) := by
  obtain ⟨M,hM⟩ := hΦ.bounded_above_of_compact_support hcΦ
  have hi : Integrable Φ := hΦ.integrable_of_hasCompactSupport hcΦ
  have H := XiPrime8845.Triple.Nu3.ratio_tendsto
    (Φ := fun n : ℕ => smoothedCertificate Φ (eps n)) (Φ₀ := Φ)
    (l := atTop) (M := 4*M) (R := 1)
    (fun n => (smoothFrequency_regular hi hcΦ (eps n).property.1
      (eps n).property.2 (n := 1)).1.continuous)
    (fun n => smoothFrequency_norm_le hM (eps n).property.1 (eps_small n))
    (fun n _ hp => smoothFrequency_eq_zero_outside_unit hhex
      (eps n).property.1 (eps n).property.2 hp)
    (smoothFrequency_tendsto_pointwise hΦ eps_small eps_tendsto) hm
  exact (Complex.continuous_re.tendsto _).comp H

theorem dyadicM3Upper_of_certificate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {c₂₀ : ℝ} (hnum : (nu3F Φ/nu3Mass Φ).re ≤ c₂₀) : DyadicM3Upper c₂₀ := by
  have hm : nu3Mass Φ = 1 := by simp [nu3Mass_eq_planeInverse_zero,hg,hg0]
  exact zetaM3_dyadic_of_certificate_limit hRH (hΦ.integrable_of_hasCompactSupport hcΦ)
    hcΦ hhex hg hgn hg0 (normalized_smoothedCertificate_tendsto hΦ hcΦ hhex
      (hm ▸ one_ne_zero)) hnum

theorem dyadicM3_limsup_of_certificate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {c₂₀ : ℝ} (hnum : (nu3F Φ/nu3Mass Φ).re ≤ c₂₀) :
    limsup (fun T => (zetaM3 T (2*T):ℝ)/(Zeta23.Ncount T (2*T):ℝ)) atTop ≤ c₂₀ :=
  limsup_countRatio_le (fun _ => Nat.cast_nonneg _) zetaNcount_dyadic_tendsto
    (dyadicM3Upper_of_certificate hRH hΦ hcΦ hhex hg hgn hg0 hnum)

theorem cumulativeM3_limsup_of_certificate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {c₂₀ : ℝ} (hc : 0 ≤ c₂₀) (hnum : (nu3F Φ/nu3Mass Φ).re ≤ c₂₀) :
    limsup (fun T => (zetaM3 0 T:ℝ)/(Zeta23.Ncount 0 T:ℝ)) atTop ≤ c₂₀ :=
  limsup_countRatio_le (fun _ => Nat.cast_nonneg _) zetaNcount_cumulative_tendsto
    (zetaM3_cumulative_upper hc (dyadicM3Upper_of_certificate hRH hΦ hcΦ hhex hg hgn hg0 hnum))

theorem simple_liminf_of_closed_certificate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {c₂₀ : ℝ} (hc : 0 ≤ c₂₀) (hnum : (nu3F Φ/nu3Mass Φ).re ≤ c₂₀) :
    1-c₂₀/3 ≤ liminf
      (fun T => (XiPrime.N0simple 0 T:ℝ)/(XiPrime.Ncount 0 T:ℝ)) atTop :=
  simple_liminf_of_factorial_bound hRH hc
    (dyadicM3Upper_of_certificate hRH hΦ hcΦ hhex hg hgn hg0 hnum)

theorem simple_liminf_ge_9742_of_d20_gate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    (hnum : (nu3F Φ/nu3Mass Φ).re ≤ 77223/1000000) :
    (0.9742:ℝ) ≤ liminf
      (fun T => (XiPrime.N0simple 0 T:ℝ)/(XiPrime.Ncount 0 T:ℝ)) atTop :=
  (show (0.9742:ℝ) ≤ 1-(77223/1000000)/3 by norm_num).trans
    (simple_liminf_of_closed_certificate hRH hΦ hcΦ hhex hg hgn hg0 (by norm_num) hnum)

end XiPrime8845.RHTripleIntegration

#print axioms XiPrime8845.RHTripleIntegration.normalized_smoothedCertificate_tendsto
#print axioms XiPrime8845.RHTripleIntegration.dyadicM3Upper_of_certificate
#print axioms XiPrime8845.RHTripleIntegration.dyadicM3_limsup_of_certificate
#print axioms XiPrime8845.RHTripleIntegration.cumulativeM3_limsup_of_certificate
#print axioms XiPrime8845.RHTripleIntegration.simple_liminf_of_closed_certificate
#print axioms XiPrime8845.RHTripleIntegration.simple_liminf_ge_9742_of_d20_gate
