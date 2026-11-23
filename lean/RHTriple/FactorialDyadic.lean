/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.FactorialMoment

/-! The dyadic upper bound with the actual ζ zero count as denominator.
The height majorant and the positive Fourier test are independent. -/

noncomputable section
open Complex Filter Topology MeasureTheory
open scoped Asymptotics

namespace XiPrime8845.RHTriple
open Zeta23 CertificateSmoothing

def UpperWithMargin (f N : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ e > 0, ∀ᶠ T in atTop, f T ≤ (c+e)*N T

def DyadicM3Upper (c : ℝ) : Prop :=
  UpperWithMargin (fun T => (zetaM3 T (2*T):ℝ)) (fun T => (Zeta23.Ncount T (2*T):ℝ)) c

theorem eventually_scale_le_dyadic_count :
    ∀ᶠ T : ℝ in atTop, T*Real.log T ≤ (4*Real.pi)*(Zeta23.Ncount T (2*T):ℝ) := by
  have hp : 0 < 4*Real.pi := by positivity
  filter_upwards [zetaDyadicCount_sub_scale_isLittleO.def (inv_pos.mpr hp),
    eventually_gt_atTop (1:ℝ)] with T hD hT
  have ht : 0 < T*Real.log T := mul_pos (by linarith) (Real.log_pos hT)
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht] at hD
  have H := (abs_le.mp hD).1
  have he : zetaMainScale T = 2*((4*Real.pi)⁻¹*(T*Real.log T)) := by
    unfold zetaMainScale
    ring
  rw [he] at H
  have hh : (4*Real.pi)⁻¹*(T*Real.log T) ≤ (Zeta23.Ncount T (2*T):ℝ) := by linarith
  have hh' : T*Real.log T/(4*Real.pi) ≤ (Zeta23.Ncount T (2*T):ℝ) := by
    simpa only [div_eq_inv_mul] using hh
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hh'

theorem zetaM3_dyadic_of_height (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hcΦ : HasCompactSupport Φ)
    {η : ℝ} (hη : 0 < η) (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2-η)
    {g : ℝ × ℝ → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {h : ℝ → ℝ} (hh : ∀ r : ℝ, paperFT k r = (h r:ℂ))
    (hhn : ∀ r, 0 ≤ h r) (hh1 : ∀ r ∈ Set.Icc (1:ℝ) 2, 1 ≤ h r) :
    DyadicM3Upper ((∫ r, (h r)^3)*(nu3F Φ).re) := by
  intro e he
  have hp : 0 < 4*Real.pi := by positivity
  have H := (zeta_smoothed_distinct_triple_main_count hRH hk hkc hΦ hcΦ hη hhex).def
    (div_pos he hp)
  filter_upwards [H, eventually_scale_le_dyadic_count, eventually_gt_atTop (1:ℝ)]
    with T hE hN hT
  have hpos : 0 < T := by linarith
  have ht : 0 < T*Real.log T := mul_pos hpos (Real.log_pos hT)
  have hcol := zetaM3_le_smoothedDistinctTriple hRH hk hkc hg hgn hg0 hh hhn hh1 hpos
  apply hcol.trans
  have hb := (Complex.re_le_norm _).trans hE
  simp only [hh, ← Complex.ofReal_pow, integral_complex_ofReal, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero,
    Real.norm_of_nonneg ht.le] at hb
  have hr : e/(4*Real.pi)*(T*Real.log T) ≤ e*(Zeta23.Ncount T (2*T):ℝ) := calc
    _ ≤ e/(4*Real.pi)*((4*Real.pi)*(Zeta23.Ncount T (2*T):ℝ)) :=
      mul_le_mul_of_nonneg_left hN (div_nonneg he.le hp.le)
    _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hp.ne']
  linarith only [hb, hr]

theorem dyadicM3Upper_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {c : ι → ℝ} {d : ℝ} (hd : Tendsto c l (𝓝 d))
    (hc : ∀ᶠ t in l, DyadicM3Upper (c t)) : DyadicM3Upper d := by
  intro e he
  have H : ∀ᶠ t in l, c t < d+e/2 := hd.eventually_lt_const (by linarith)
  obtain ⟨t, ht, hh⟩ := (hc.and H).exists
  filter_upwards [ht (e/2) (by positivity)] with T hT
  exact hT.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.zetaM3_dyadic_of_height
#print axioms XiPrime8845.RHTriple.dyadicM3Upper_of_tendsto
