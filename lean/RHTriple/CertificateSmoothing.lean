/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.ExplicitProduct
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Smooth interior approximants for the closed-hexagon GdLL witness.
Unlike the order used in GdLL v2 §2, we contract before smoothing,
and reserve an explicit positive margin for the triple formula. -/

noncomputable section
open MeasureTheory Set
open scoped Convolution Pointwise

namespace XiPrime8845.RHTriple
namespace CertificateSmoothing

abbrev Plane := ℝ × ℝ

def hexGauge (p : Plane) : ℝ := |p.1| + |p.2| + |p.1+p.2|

theorem hexGauge_add_le (p q : Plane) : hexGauge (p+q) ≤ hexGauge p + hexGauge q := by
  simp only [hexGauge, Prod.fst_add, Prod.snd_add]
  rw [show p.1+q.1+(p.2+q.2) = (p.1+p.2)+(q.1+q.2) by ring]
  linarith only [abs_add_le p.1 q.1, abs_add_le p.2 q.2, abs_add_le (p.1+p.2) (q.1+q.2)]

theorem hexGauge_smul (a : ℝ) (p : Plane) : hexGauge (a • p) = |a| * hexGauge p := by
  simp only [hexGauge, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← mul_add, abs_mul]

theorem hexGauge_le_four_norm (p : Plane) : hexGauge p ≤ 4*‖p‖ := by
  have h₁ : |p.1| ≤ ‖p‖ := by simp [Prod.norm_def, Real.norm_eq_abs]
  have h₂ : |p.2| ≤ ‖p‖ := by simp [Prod.norm_def, Real.norm_eq_abs]
  unfold hexGauge
  linarith only [h₁, h₂, abs_add_le p.1 p.2]

def planeConvolution (f g : Plane → ℂ) : Plane → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℂ] g

theorem hexGauge_convolution {f g : Plane → ℂ} {R S : ℝ}
    (hf : ∀ p, f p ≠ 0 → hexGauge p ≤ R)
    (hg : ∀ p, g p ≠ 0 → hexGauge p ≤ S) {p : Plane}
    (hp : planeConvolution f g p ≠ 0) : hexGauge p ≤ R+S := by
  have hh : p ∈ Function.support f + Function.support g :=
    MeasureTheory.support_convolution_subset (ContinuousLinearMap.mul ℝ ℂ) hp
  obtain ⟨x,hx,y,hy,rfl⟩ := Set.mem_add.mp hh
  exact (hexGauge_add_le x y).trans (add_le_add (hf x hx) (hg y hy))

def contract (Φ : Plane → ℂ) (a : ℝ) (p : Plane) : ℂ :=
  ((a : ℂ)^2)⁻¹ * Φ (a⁻¹ • p)

def mollifierSeed (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Plane) :=
  ⟨ε/16, ε/8, by positivity, by linarith⟩

def mollifier (ε : ℝ) (hε : 0 < ε) (p : Plane) : ℂ :=
  ((mollifierSeed ε hε).normed volume p : ℝ)

theorem mollifier_contDiff (ε : ℝ) (hε : 0 < ε) {n : ℕ∞} :
    ContDiff ℝ n (mollifier ε hε) :=
  Complex.ofRealCLM.contDiff.comp (mollifierSeed ε hε).contDiff_normed

theorem mollifier_compact (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (mollifier ε hε) := by
  apply (mollifierSeed ε hε).hasCompactSupport_normed.comp_left
  simp

theorem mollifier_hex {ε : ℝ} (hε : 0 < ε) {p : Plane}
    (hp : mollifier ε hε p ≠ 0) : hexGauge p ≤ ε/2 := by
  have H : p ∈ Function.support ((mollifierSeed ε hε).normed volume) :=
    fun hz => hp (by simp [mollifier, hz])
  rw [ContDiffBump.support_normed_eq] at H
  have hh : ‖p‖ < ε/8 := by simpa [Metric.mem_ball, dist_zero_right, mollifierSeed] using H
  exact (hexGauge_le_four_norm p).trans (by linarith)

def smoothingKernel (ε : ℝ) (hε : 0 < ε) : Plane → ℂ :=
  planeConvolution (mollifier ε hε) (mollifier ε hε)

def smoothFrequency (Φ : Plane → ℂ) (ε : ℝ) (hε : 0 < ε) : Plane → ℂ :=
  planeConvolution (contract Φ (1-ε)) (smoothingKernel ε hε)

theorem smoothFrequency_regular {Φ : Plane → ℂ} (hΦ : Integrable Φ)
    (hcΦ : HasCompactSupport Φ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {n : ℕ∞} :
    ContDiff ℝ n (smoothFrequency Φ ε hε) ∧ HasCompactSupport (smoothFrequency Φ ε hε) := by
  let B := ContinuousLinearMap.mul ℝ ℂ
  have ha : 0 < 1-ε := by linarith
  have hca : HasCompactSupport (contract Φ (1-ε)) := by
    apply (hcΦ.comp_homeomorph (Homeomorph.smul (Units.mk0 (1-ε)⁻¹ (inv_ne_zero ha.ne')))).mul_left
  have hia : Integrable (contract Φ (1-ε)) := (hΦ.comp_smul (inv_ne_zero ha.ne')).const_mul _
  have hcφ := mollifier_compact ε hε
  have hφ := mollifier_contDiff ε hε (n := n)
  have hiφ := hφ.continuous.integrable_of_hasCompactSupport (μ := (volume : Measure Plane)) hcφ
  have hcψ : HasCompactSupport (smoothingKernel ε hε) := hcφ.convolution B hcφ
  have hψ : ContDiff ℝ n (smoothingKernel ε hε) :=
    hcφ.contDiff_convolution_right B hiφ.locallyIntegrable hφ
  exact ⟨hcψ.contDiff_convolution_right B hia.locallyIntegrable hψ, hca.convolution B hcψ⟩

theorem smoothFrequency_margin {Φ : Plane → ℂ}
    (hΦ : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (p : Plane) (hp : smoothFrequency Φ ε hε p ≠ 0) : hexGauge p ≤ 2-ε := by
  let a := 1-ε
  have ha : 0 < a := by dsimp [a]; linarith
  have hscaled (q : Plane) (hq : contract Φ a q ≠ 0) : hexGauge q ≤ 2*a := by
    have ht : Φ (a⁻¹ • q) ≠ 0 := fun h => hq (by simp [contract,h])
    have hh := hΦ _ ht
    rw [hexGauge_smul, abs_of_pos (inv_pos.mpr ha), ← div_eq_inv_mul] at hh
    exact (div_le_iff₀ ha).mp hh
  have hkernel (q : Plane) (hq : smoothingKernel ε hε q ≠ 0) : hexGauge q ≤ ε := by
    have hh := hexGauge_convolution (fun p => mollifier_hex hε (p := p))
      (fun p => mollifier_hex hε (p := p)) hq
    linarith only [hh]
  have hh := hexGauge_convolution hscaled hkernel hp
  dsimp [a] at hh
  linarith only [hh]

end CertificateSmoothing
end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.CertificateSmoothing.smoothFrequency_regular
#print axioms XiPrime8845.RHTriple.CertificateSmoothing.smoothFrequency_margin
