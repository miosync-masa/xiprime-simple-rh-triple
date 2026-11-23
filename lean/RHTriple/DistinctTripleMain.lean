/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.ZetaSlotSieve
import RHTriple.Nu3SieveMain
import RHTriple.SingletonMain

/-! The smoothed full-height ζ three-point theorem on distinct slots.
This does not unsmooth height, bound the cumulative M₃ count, or use
the finite numerical certificate. -/

noncomputable section
open Complex Filter Topology MeasureTheory
open scoped Asymptotics

namespace XiPrime8845.RHTriple
open Zeta23

theorem slotCubeMass_main_count (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    (fun T => slotCubeMass k T - (∫ r : ℝ, (paperFT k r)^3) * (Zeta23.Ncount T (2*T):ℂ))
      =o[atTop] (fun T => T*Real.log T) := by
  let A := ∫ r : ℝ, (paperFT k r)^3
  have H := zeta_singleton_cube_normalized_tendsto hRH hk hkc
  change Tendsto (fun T => slotCubeMass k T / ((T*Real.log T:ℝ):ℂ))
    atTop (𝓝 (A/(2*Real.pi))) at H
  have hne : ∀ᶠ T : ℝ in atTop, ((T*Real.log T:ℝ):ℂ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact_mod_cast mul_ne_zero (show T ≠ 0 by linarith) (Real.log_pos hT).ne'
  have HE := H.sub_const (A/(2*Real.pi))
  rw [sub_self] at HE
  have hscale : (fun T => slotCubeMass k T - A*(zetaMainScale T:ℂ)) =o[atTop]
      (fun T => ((T*Real.log T:ℝ):ℂ)) := by
    refine Asymptotics.isLittleO_of_tendsto' (hne.mono fun T ht he => (ht he).elim)
      (HE.congr' ?_)
    filter_upwards [hne] with T hT
    change slotCubeMass k T / ((T*Real.log T:ℝ):ℂ)-A/(2*Real.pi) =
      (slotCubeMass k T-A*(zetaMainScale T:ℂ))/((T*Real.log T:ℝ):ℂ)
    rw [sub_div, show A*(zetaMainScale T:ℂ) / ((T*Real.log T:ℝ):ℂ) =
      A/(2*Real.pi) by
        unfold zetaMainScale
        push_cast at hT ⊢
        field_simp [Real.pi_ne_zero]
        rw [mul_assoc, mul_div_cancel_right₀ _ hT]]
  have hreal : (fun T => slotCubeMass k T - A*(zetaMainScale T:ℂ)) =o[atTop]
      (fun T => T*Real.log T) :=
    (hscale.norm_right.congr_right (fun T => Complex.norm_real (T*Real.log T))).of_norm_right
  refine (hreal.sub (zetaDyadicCount_sub_scale_isLittleO.const_mul_left A)).congr_left ?_
  intro T
  change slotCubeMass k T-A*(zetaMainScale T:ℂ) -
    A*((Zeta23.Ncount T (2*T):ℂ)-(zetaMainScale T:ℂ)) = _
  ring

/-- The full-height sum over ordered, pairwise distinct ζ slots has
the Fourier-side GdLL main term, with cubic height mass and the actual
dyadic ζ count. Distinct slots at a repeated zero are not excluded. -/
theorem zeta_smoothed_distinct_triple_main_count (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hcΦ : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    (fun T => smoothedDistinctTriple k Φ T - (∫ r : ℝ, (paperFT k r)^3) *
      (Zeta23.Ncount T (2*T):ℂ) * nu3F Φ) =o[atTop] (fun T => T*Real.log T) := by
  have h₃ := zeta_smoothed_triple_main_count hRH hk hkc hΦ hcΦ hη hhex
  obtain ⟨hp₁,hp₂,hp₃⟩ := zeta_three_collapsed_pair_limits hRH hk hkc hΦ hη hhex
  have h₁ := (slotCubeMass_main_count hRH hk hkc).const_mul_left (2*nu3Mass Φ)
  have H := (((h₃.sub hp₁).sub hp₂).sub hp₃).add h₁
  refine H.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  have hc := inclusion_exclusion_main_eq_nu3F hΦ.continuous hcΦ hη hhex
  rw [smoothedDistinctTriple_eq_sieve hRH hk hkc hΦ hcΦ hη hhex hT, ← hc]
  unfold collapsedPairMain nu3Mass
  ring

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.slotCubeMass_main_count
#print axioms XiPrime8845.RHTriple.zeta_smoothed_distinct_triple_main_count
