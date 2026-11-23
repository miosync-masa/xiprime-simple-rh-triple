/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTripleIntegration.CertificateNormalize
import TripleCorrelation.CertFinal

/-! The explicit d = 20 certificate now supplies the analytical endgame.
The ζ and ξ′ counts are the actual AF counts, and RH is the only
mathematical hypothesis of the final two theorems. -/

noncomputable section
open Complex Filter Set
open XiPrime8845.RHTriple XiPrime8845.RHTriple.CertificateSmoothing

namespace XiPrime8845.RHTripleIntegration
open XiPrime8845.Triple (P20i P20_nu3)
open XiPrime8845.Triple.Region (pOf Fof Phi0 mF)
open XiPrime8845.Triple.Sym (pOf_continuous integrable_F Phi0_mass mass_ofReal)

def c20 : ℝ := 77223 / 1000000

private def p20Frequency (p : Plane) : ℂ := Phi0 (pOf P20i) p

private theorem p20Frequency_continuous : Continuous p20Frequency :=
  P20_nu3.1

private theorem p20Frequency_hex (p : Plane) (hp : p20Frequency p ≠ 0) :
    hexGauge p ≤ 2 :=
  P20_nu3.2.1 p hp

private theorem p20Frequency_compact : HasCompactSupport p20Frequency := by
  refine HasCompactSupport.intro (isCompact_closedBall (0:Plane) 2) fun p hp => ?_
  by_contra h
  have H := p20Frequency_hex p h
  unfold hexGauge at H
  apply hp
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff,
    Real.norm_eq_abs, Real.norm_eq_abs]
  constructor <;> linarith [abs_nonneg p.1, abs_nonneg p.2, abs_nonneg (p.1+p.2)]

private theorem p20Frequency_inverse (x : Plane) :
    planeInverse p20Frequency x =
      (‖planeInverse (fun p => (Fof (pOf P20i) p : ℂ)) x‖^2 : ℝ) :=
  planeInverse_real_autocorrelation (integrable_F (pOf_continuous P20i)) x

private theorem p20Frequency_inverse_zero_pos : 0 < (planeInverse p20Frequency 0).re := by
  have hm : nu3Mass p20Frequency ≠ 0 := P20_nu3.2.2.1
  have H : nu3Mass p20Frequency = ((mF (pOf P20i)^2 : ℝ):ℂ) := by
    change XiPrime8845.Triple.Nu3.mass (fun p => (Phi0 (pOf P20i) p : ℂ)) = _
    rw [mass_ofReal, Phi0_mass (pOf_continuous P20i)]
  have hne : mF (pOf P20i) ≠ 0 := by
    intro hz
    exact hm (by simp [H,hz])
  rw [← nu3Mass_eq_planeInverse_zero, H, ofReal_re]
  exact sq_pos_of_ne_zero hne

/-- Under RH, the lower limiting share of ξ′ zeros which are simple and
on the critical line is at least `1 - c20 / 3`. -/
theorem xiPrime_simple_proportion_c20 (hRH : RiemannHypothesis) :
    1-c20/3 ≤ liminf (fun T => (Zeta23.XiPrime.N0simple 0 T : ℝ) /
      (Zeta23.XiPrime.Ncount 0 T : ℝ)) atTop := by
  apply simple_liminf_of_unnormalized_certificate hRH p20Frequency_continuous
    p20Frequency_compact p20Frequency_hex
  · intro p
    rw [p20Frequency_inverse, ofReal_im]
  · intro p
    rw [p20Frequency_inverse, ofReal_re]
    exact sq_nonneg _
  · exact p20Frequency_inverse_zero_pos
  · norm_num [c20]
  · exact P20_nu3.2.2.2

/-- The exact c20 bound implies at least 97.42 percent. -/
theorem xiPrime_simple_proportion_ge_9742 (hRH : RiemannHypothesis) :
    (0.9742 : ℝ) ≤ liminf (fun T => (Zeta23.XiPrime.N0simple 0 T : ℝ) /
      (Zeta23.XiPrime.Ncount 0 T : ℝ)) atTop :=
  (show (0.9742 : ℝ) ≤ 1-c20/3 by norm_num [c20]).trans
    (xiPrime_simple_proportion_c20 hRH)

end XiPrime8845.RHTripleIntegration

#check XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_c20
#check XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_ge_9742
#print axioms XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_c20
#print axioms XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_ge_9742
