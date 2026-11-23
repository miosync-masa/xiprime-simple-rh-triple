/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedSupport

/-! Exact changes of variables for permuting the three frequency slots.
The second change is a reflection followed by a translation on each fibre. -/

noncomputable section
open Complex MeasureTheory Filter

namespace XiPrime8845.RHTriple

def swap01 : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.prodComm ℝ ℝ

def swap12 : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := (x.1, -(x.1+x.2))
  invFun x := (x.1, -(x.1+x.2))
  left_inv x := Prod.ext rfl (by ring)
  right_inv x := Prod.ext rfl (by ring)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem integral_swap01 (F : ℝ × ℝ → ℂ) :
    (∫ x, F (swap01 x)) = ∫ x, F x := integral_prod_swap F

theorem integral_swap12 {F : ℝ × ℝ → ℂ}
    (hF : Continuous F) (hcF : HasCompactSupport F) :
    (∫ x, F (swap12 x)) = ∫ x, F x := by
  have h₁ : Integrable F := hF.integrable_of_hasCompactSupport hcF
  have h₂ : Integrable (F ∘ swap12) :=
    (hF.comp swap12.continuous).integrable_of_hasCompactSupport (hcF.comp_homeomorph swap12)
  change (∫ x, (F ∘ swap12) x ∂(volume.prod volume)) = ∫ x, F x ∂(volume.prod volume)
  rw [integral_prod _ h₂, integral_prod _ h₁]
  apply integral_congr_ae
  filter_upwards [] with u
  change (∫ v : ℝ, F (u, -(u+v))) = ∫ v : ℝ, F (u,v)
  simp_rw [show ∀ v : ℝ, -(u+v) = (-1)*v+(-u) by intro v; ring]
  rw [Measure.integral_comp_mul_left (fun v : ℝ => F (u, v+(-u))) (-1)]
  simpa only [inv_neg, inv_one, abs_neg, abs_one, one_smul] using
    (integral_add_right_eq_self (fun v : ℝ => F (u,v)) (-u))

theorem slots_swap01 (L : ℝ) (x : ℝ × ℝ) :
    frequencyShift L 0 (swap01 x) = frequencyShift L 1 x ∧
    frequencyShift L 1 (swap01 x) = frequencyShift L 0 x ∧
    frequencyShift L 2 (swap01 x) = frequencyShift L 2 x := by
  refine ⟨rfl, rfl, ?_⟩
  change -(L*x.2+L*x.1) = -(L*x.1+L*x.2)
  ring

theorem slots_swap12 (L : ℝ) (x : ℝ × ℝ) :
    frequencyShift L 0 (swap12 x) = frequencyShift L 0 x ∧
    frequencyShift L 1 (swap12 x) = frequencyShift L 2 x ∧
    frequencyShift L 2 (swap12 x) = frequencyShift L 1 x := by
  refine ⟨rfl, ?_, ?_⟩
  · change L*(-(x.1+x.2)) = -(L*x.1+L*x.2)
    ring
  · change -(L*x.1+L*(-(x.1+x.2))) = L*x.2
    ring

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.integral_swap01
#print axioms XiPrime8845.RHTriple.integral_swap12
#print axioms XiPrime8845.RHTriple.slots_swap01
#print axioms XiPrime8845.RHTriple.slots_swap12
