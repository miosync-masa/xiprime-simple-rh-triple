/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.ExplicitProduct
import Zeta23.RvM.Statement
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The actual dyadic ζ zero count is interchangeable with the
Rudnick–Sarnak normalization T log T/(2π) at the precision here. -/

noncomputable section
open Complex Filter Topology
open scoped Asymptotics

namespace XiPrime8845.RHTriple
open Zeta23

def zetaMainScale (T : ℝ) : ℝ := T*Real.log T/(2*Real.pi)

theorem zetaDyadicCount_sub_scale_isLittleO :
    (fun T => ((Zeta23.Ncount T (2*T) : ℕ):ℂ) - (zetaMainScale T : ℂ))
      =o[atTop] (fun T => T*Real.log T) := by
  obtain ⟨C,T₀,hC⟩ := (RvM.riemannVonMangoldt gammaFacts).main
  let D := 2*Real.log 2-1-Real.log (2*Real.pi)
  let f (T : ℝ) := (Zeta23.Ncount T (2*T):ℝ) - zetaMainScale T
  have hp : 0 < 2*Real.pi := by positivity
  have hzero : Tendsto (fun T => |C|/T + (|D|/(2*Real.pi))/Real.log T) atTop (𝓝 0) := by
    have h₁ := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).const_mul |C|
    have h₂ := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (|D|/(2*Real.pi))
    simpa only [Function.comp_apply, ← div_eq_mul_inv, mul_zero, add_zero] using h₁.add h₂
  have hb : Tendsto (fun T => f T/(T*Real.log T)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hzero
    filter_upwards [eventually_ge_atTop T₀, eventually_gt_atTop (1:ℝ)] with T hT₀ hT
    have ht : 0 < T := by linarith
    have hl := Real.log_pos hT
    have hs : ell1 T = Real.log T + D := by
      unfold ell1 l D
      rw [Real.log_div ht.ne' hp.ne']
      ring
    have hh : ‖(Zeta23.Ncount T (2*T):ℝ) - T/(2*Real.pi)*ell1 T‖ ≤ |C| * Real.log T := by
      rw [Real.norm_eq_abs]
      exact (hC T hT₀).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hl.le)
    have hD : ‖T/(2*Real.pi)*(D)‖ = T/(2*Real.pi) * |D| := by
      rw [norm_mul, Real.norm_of_nonneg (div_nonneg ht.le hp.le), Real.norm_eq_abs]
    have hf : ‖f T‖ ≤ |C| * Real.log T + T/(2*Real.pi) * |D| := by
      have he : f T = ((Zeta23.Ncount T (2*T):ℝ) - T/(2*Real.pi)*ell1 T) + T/(2*Real.pi)*D := by
        unfold f zetaMainScale
        rw [hs]
        ring
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add hh hD.le)
    rw [norm_div, Real.norm_of_nonneg (mul_nonneg ht.le hl.le)]
    calc
      _ ≤ (|C| * Real.log T + T/(2*Real.pi) * |D|)/(T*Real.log T) :=
        div_le_div_of_nonneg_right hf (by positivity)
      _ = _ := by field_simp [hp.ne']
  have H : f =o[atTop] (fun T => T*Real.log T) :=
    Asymptotics.isLittleO_of_tendsto'
      ((eventually_gt_atTop (1:ℝ)).mono fun T hT hz =>
        ((mul_pos (by linarith) (Real.log_pos hT)).ne' hz).elim) hb
  rw [← Asymptotics.isLittleO_norm_left] at H ⊢
  refine H.congr_left fun T => ?_
  unfold f
  rw [← Complex.norm_real]
  push_cast
  rfl

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.zetaDyadicCount_sub_scale_isLittleO
