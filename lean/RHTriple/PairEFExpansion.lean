/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairIntegrated
import RHTriple.PairGammaMain

/-! An exact mixed-height two-slot expansion with a single strict
prime cutoff shared by the two height profiles. -/

noncomputable section
open Complex MeasureTheory Filter

namespace XiPrime8845.RHTriple
open Zeta23

def pairEFfactor (k : ℝ → ℂ) (d T t : ℝ) : ℂ :=
  poleFactor (dilate k T) (Real.log T*t) +
    primeFactor (dilate k T) (d*Real.log T) (Real.log T*t) +
    gammaFactor (dilate k T) (Real.log T*t)

theorem smoothedPair_eventually_eq_factors (hRH : RiemannHypothesis)
    {a b Q : ℝ → ℂ}
    (ha : ContDiff ℝ 2 a) (hca : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hcb : HasCompactSupport b)
    (hQ : Integrable Q) {c d : ℝ} (hcd : c < d)
    (hs : ∀ t, Q t ≠ 0 → |t| ≤ c) :
    ∀ᶠ T : ℝ in atTop, smoothedPair a b Q T =
      ∫ t : ℝ, Q t * (pairEFfactor a d T t * pairEFfactor b d T (-t)) := by
  obtain ⟨R₁,h₁⟩ := EF.exists_abs_le_of_hasCompactSupport hca
  obtain ⟨R₂,h₂⟩ := EF.exists_abs_le_of_hasCompactSupport hcb
  let R := max (max R₁ R₂) 0
  have hR : 0 ≤ R := le_max_right _ _
  have lem {k : ℝ → ℂ} (hk : ∀ x, k x ≠ 0 → |x| ≤ R) {T : ℝ} (ht : 0 < T) :
      ∀ x, dilate k T x ≠ 0 → |x| ≤ R/T := by
    intro x hx
    have hh := hk (T*x) (fun hz => hx (by simp [dilate,hz]))
    rw [abs_mul, abs_of_pos ht, mul_comm T] at hh
    exact (le_div_iff₀ ht).2 hh
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop R,
    Real.tendsto_log_atTop.eventually_ge_atTop (1/(d-c))] with T hT hTR hTlog
  have ht : 0 < T := by linarith
  have hL := Real.log_pos hT
  have hRL : R/T ≤ (d-c)*Real.log T := by
    exact ((div_le_one ht).2 hTR).trans
      (by simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr hcd)).1 hTlog)
  rw [smoothedPair_eq_integral_EF hRH ha hca hb hcb hQ ht]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hq : Q t = 0
  · simp [hq]
  have hcap : R/T + |Real.log T*t| ≤ d*Real.log T := by
    rw [abs_mul, abs_of_pos hL]
    have H := mul_le_mul_of_nonneg_left (hs t hq) hL.le
    nlinarith only [hRL,H]
  have hcap' : R/T + |-(Real.log T*t)| ≤ d*Real.log T := by rw [abs_neg]; exact hcap
  rw [literatureRHS_split
       (lem (fun x hx => (h₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))) ht) hcap,
      literatureRHS_split
       (lem (fun x hx => (h₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _))) ht) hcap']
  simp only [pairEFfactor,mul_neg]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.smoothedPair_eventually_eq_factors
