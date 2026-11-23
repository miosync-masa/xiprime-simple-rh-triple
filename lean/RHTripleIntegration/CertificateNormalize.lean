/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTripleIntegration.CertificateLimit

/-! Accept the certificate branch's unnormalized autocorrelation.
Dividing by its positive inverse value at zero does not change the gate. -/

noncomputable section
open Complex Filter MeasureTheory
open XiPrime8845.RHTriple XiPrime8845.RHTriple.CertificateSmoothing

namespace XiPrime8845.RHTripleIntegration
open Zeta23

private theorem planeInverse_const_mul (Φ : Plane → ℂ) (a : ℂ) (p : Plane) :
    planeInverse (fun q => a*Φ q) p = a*planeInverse Φ p := by
  simp_rw [planeInverse,mul_assoc,integral_const_mul]

private theorem nu3Mass_const_mul (Φ : Plane → ℂ) (a : ℂ) :
    nu3Mass (fun q => a*Φ q) = a*nu3Mass Φ := integral_const_mul a _

private theorem nu3F_const_mul (Φ : Plane → ℂ) (a : ℂ) :
    nu3F (fun q => a*Φ q) = a*nu3F Φ := by
  have hline (ℓ : ℝ → Plane) : lineInt (fun q => a*Φ q) ℓ = a*lineInt Φ ℓ := by
    unfold lineInt
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have hweight : (∫ ξ : Plane, (nu3Kernel ξ:ℂ)*(a*Φ ξ)) =
      a*(∫ ξ : Plane, (nu3Kernel ξ:ℂ)*Φ ξ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  unfold nu3F
  rw [hline,hline,hline,hweight]
  ring

theorem simple_liminf_of_unnormalized_certificate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    (hreal : ∀ p, (planeInverse Φ p).im = 0)
    (hn : ∀ p, 0 ≤ (planeInverse Φ p).re) (hm : 0 < (planeInverse Φ 0).re)
    {c₂₀ : ℝ} (hc : 0 ≤ c₂₀) (hnum : (nu3F Φ/nu3Mass Φ).re ≤ c₂₀) :
    1-c₂₀/3 ≤ liminf
      (fun T => (XiPrime.N0simple 0 T:ℝ)/(XiPrime.Ncount 0 T:ℝ)) atTop := by
  let A := (planeInverse Φ 0).re
  let Ψ (p : Plane) := ((A⁻¹:ℝ):ℂ)*Φ p
  have hA : 0 < A := hm
  have hAc : ((A⁻¹:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (inv_ne_zero hA.ne')
  let g (p : Plane) := A⁻¹*(planeInverse Φ p).re
  have hgp (p : Plane) : planeInverse Ψ p = (g p:ℂ) := by
    have he : planeInverse Φ p = ((planeInverse Φ p).re:ℂ) :=
      Complex.ext rfl (by simpa using hreal p)
    unfold Ψ
    rw [planeInverse_const_mul, he]
    exact (ofReal_mul ..).symm
  have hzg : g 0 = 1 := inv_mul_cancel₀ hA.ne'
  have hrat : nu3F Ψ/nu3Mass Ψ = nu3F Φ/nu3Mass Φ := by
    unfold Ψ
    rw [nu3F_const_mul, nu3Mass_const_mul, mul_div_mul_left _ _ hAc]
  exact simple_liminf_of_closed_certificate hRH (Φ := Ψ) (continuous_const.mul hΦ) hcΦ.mul_left
    (fun p hp => hhex p (fun h => hp (by simp [Ψ,h]))) hgp
    (fun p => mul_nonneg (inv_nonneg.mpr hA.le) (hn p)) hzg hc
    (by rwa [hrat])

end XiPrime8845.RHTripleIntegration

#print axioms XiPrime8845.RHTripleIntegration.simple_liminf_of_unnormalized_certificate
