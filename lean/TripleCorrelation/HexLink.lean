/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.SemCheck
import TripleCorrelation.Hexagon

/-! # `i0`, `i2` are integrals over the doubled hexagon

`sqR (S0 Pt) = ∫_{hexD} P̃` and `sqR (S2 Pt) = ∫_{hexD} P̃²` (`sqR_S0`, `sqR_S2`), for every
integer table `Pt`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region
open IntCheck IntCheck.Sem

theorem PR_continuous (Pt : List (List Int)) : Continuous fun z : ℝ × ℝ => PR Pt z.1 z.2 := by
  unfold PR IntCheck.evalBiv
  induction Pt with
  | nil => exact continuous_const
  | cons row Pt ih =>
    refine Continuous.add ?_ (continuous_fst.mul ih)
    induction row with
    | nil => exact continuous_const
    | cons c row ihr => exact continuous_const.add (continuous_snd.mul ihr)

theorem integral_sqC {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∫ z in sqC, f z = ∫ y in (0 : ℝ)..1, ∫ x in (-1 : ℝ)..0, f (x, y) := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) := isCompact_Icc.prod isCompact_Icc
  have hint : IntegrableOn (fun w : ℝ × ℝ => f w.swap) (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact (hf.comp continuous_swap).continuousOn.integrableOn_compact hK
  unfold sqC
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, setIntegral_prod _ hint,
    intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  rfl

theorem sqR_eq (W : ℝ × ℝ × Unit → ℝ) :
    sqR W = ∫ y in (0 : ℝ)..1, ∫ x in (-1 : ℝ)..0, W (x, (y, ())) := by
  simp [sqR, XYR]

theorem sqR_of_rot {W : ℝ × ℝ → ℝ} (hW : Continuous W) (S : ℝ × ℝ × Unit → ℝ)
    (hS : ∀ x y, S (x, (y, ())) = W (x, y) + (W (σ (x, y)) + W (σ2 (x, y)))) :
    sqR S = ∫ z in hexD, W z := by
  have h1 : Continuous fun z => W (σ z) := hW.comp (by unfold σ; fun_prop)
  have h2 : Continuous fun z => W (σ2 z) := hW.comp (by unfold σ2; fun_prop)
  have hc : IsCompact sqC := isCompact_Icc.prod isCompact_Icc
  have i0 := hW.continuousOn.integrableOn_compact hc (μ := volume)
  have i1 := h1.continuousOn.integrableOn_compact hc (μ := volume)
  have i2 := h2.continuousOn.integrableOn_compact hc (μ := volume)
  have i12 : IntegrableOn (fun z => W (σ z) + W (σ2 z)) sqC := i1.add i2
  have a1 := integral_add i0 i12
  have a2 := integral_add i1 i2
  beta_reduce at a1 a2
  have hsum : Continuous fun z => W z + (W (σ z) + W (σ2 z)) := hW.add (h1.add h2)
  rw [integral_hexD hW, add_assoc, ← a2, ← a1, integral_sqC hsum, sqR_eq]
  simp only [hS]

theorem sqR_S0 (Pt : List (List Int)) : sqR (S0 Pt) = ∫ z in hexD, PR Pt z.1 z.2 := by
  refine sqR_of_rot (PR_continuous Pt) _ fun x y => ?_
  simp only [S0, σ, σ2]; ring_nf

theorem sqR_S2 (Pt : List (List Int)) :
    sqR (S2 Pt) = ∫ z in hexD, PR Pt z.1 z.2 * PR Pt z.1 z.2 := by
  refine sqR_of_rot (W := fun z => PR Pt z.1 z.2 * PR Pt z.1 z.2)
    ((PR_continuous Pt).mul (PR_continuous Pt)) _ fun x y => ?_
  simp only [S2, σ, σ2]; ring_nf

end XiPrime8845.Triple.Region

#print axioms XiPrime8845.Triple.Region.sqR_S0
#print axioms XiPrime8845.Triple.Region.sqR_S2
