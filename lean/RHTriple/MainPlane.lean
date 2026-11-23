/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.GammaLimit
import RHTriple.MixedSlots

/-! A normalized frequency-plane integral along `x+y+z=0`, with the
Jacobian for the two independent variables made explicit. -/

noncomputable section
open Complex MeasureTheory Filter Topology

namespace XiPrime8845.RHTriple

def planeProduct (Φ : ℝ × ℝ → ℂ) (A B C : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ × ℝ, Φ x * (A x.1 * B x.2 * C (-(x.1+x.2)))

theorem planeProduct_integrable {Φ : ℝ × ℝ → ℂ} {A B C : ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hA : Continuous A)
    (hB : Continuous B) (hC : Continuous C) :
    Integrable fun x : ℝ × ℝ => Φ x * (A x.1 * B x.2 * C (-(x.1+x.2))) := by
  exact (hΦ.mul (((hA.comp continuous_fst).mul (hB.comp continuous_snd)).mul
    (hC.comp (continuous_fst.add continuous_snd).neg))).integrable_of_hasCompactSupport hΦc.mul_right

theorem planeProduct_bound {Φ : ℝ × ℝ → ℂ} {A B C : ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hA : Continuous A)
    (hB : Continuous B) (hC : Continuous C) (hAi : Integrable A) (hBi : Integrable B) {M e : ℝ}
    (hM : 0 ≤ M) (he : 0 ≤ e) (hMb : ∀ x, ‖Φ x‖ ≤ M) (hEb : ∀ x, ‖C x‖ ≤ e) :
    ‖planeProduct Φ A B C‖ ≤ (M*e) * ((∫ x, ‖A x‖)*(∫ y, ‖B y‖)) := by
  have hi := planeProduct_integrable hΦ hΦc hA hB hC
  have hdi := (hAi.norm.mul_prod hBi.norm).const_mul (M*e)
  unfold planeProduct
  calc
    _ ≤ ∫ x : ℝ × ℝ, ‖Φ x * (A x.1 * B x.2 * C (-(x.1+x.2)))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ × ℝ, (M*e)*(‖A x.1‖*‖B x.2‖) := by
      apply integral_mono hi.norm hdi
      intro x
      change ‖Φ x * (A x.1 * B x.2 * C (-(x.1+x.2)))‖ ≤ (M*e)*(‖A x.1‖*‖B x.2‖)
      rw [show (M*e)*(‖A x.1‖*‖B x.2‖) = M*(‖A x.1‖*‖B x.2‖*e) by ring]
      simp only [norm_mul]
      gcongr
      · exact hMb x
      · exact hEb _
    _ = _ := by
      rw [integral_const_mul]
      change (M*e)*(∫ x : ℝ × ℝ, ‖A x.1‖*‖B x.2‖ ∂(volume.prod volume)) = _
      rw [integral_prod_mul (fun x => ‖A x‖) (fun y => ‖B y‖)]

theorem planeProduct_swap01 (Φ : ℝ × ℝ → ℂ) (A B C : ℝ → ℂ) :
    planeProduct Φ A B C = planeProduct (Φ ∘ swap01) B A C := by
  unfold planeProduct
  rw [← integral_swap01]
  apply integral_congr_ae
  filter_upwards [] with x
  change Φ (swap01 x)*(A x.2*B x.1*C (-(x.2+x.1))) =
    Φ (swap01 x)*(B x.1*A x.2*C (-(x.1+x.2)))
  rw [add_comm x.2 x.1, mul_comm (A x.2)]

theorem planeProduct_swap12 {Φ : ℝ × ℝ → ℂ} {A B C : ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hA : Continuous A)
    (hB : Continuous B) (hC : Continuous C) :
    planeProduct Φ A B C = planeProduct (Φ ∘ swap12) A C B := by
  let F (x : ℝ × ℝ) := Φ x * (A x.1*B x.2*C (-(x.1+x.2)))
  have hF : Continuous F := by unfold F; fun_prop
  calc
    _ = ∫ x, F (swap12 x) := (integral_swap12 hF
      (hΦc.mul_right : HasCompactSupport F)).symm
    _ = _ := by
      unfold planeProduct
      apply integral_congr_ae
      filter_upwards [] with x
      change Φ (swap12 x)*(A x.1*B (-(x.1+x.2))*C (-(x.1+ -(x.1+x.2)))) =
        Φ (swap12 x)*(A x.1*C x.2*B (-(x.1+x.2)))
      rw [show -(x.1+ -(x.1+x.2)) = x.2 by ring]
      ring

def planeAffine (a : ℝ × ℝ) (d : ℝ) (hd : d ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun x := (d*x.1+a.1, d*x.2+a.2)
  invFun x := ((x.1-a.1)/d, (x.2-a.2)/d)
  left_inv x := by ext <;> dsimp <;> field_simp <;> ring
  right_inv x := by ext <;> dsimp <;> field_simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem planeAffine_integral {F : ℝ × ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (a : ℝ × ℝ) {d : ℝ} (hd : d ≠ 0) :
    (∫ x, F (planeAffine a d hd x)) = |d⁻¹|^2 • ∫ x, F x := by
  have h₁ : Integrable F := hF.integrable_of_hasCompactSupport hFc
  have h₂ : Integrable (F ∘ planeAffine a d hd) :=
    (hF.comp (planeAffine a d hd).continuous).integrable_of_hasCompactSupport
      (hFc.comp_homeomorph (planeAffine a d hd))
  change (∫ x, (F ∘ planeAffine a d hd) x ∂(volume.prod volume)) =
    |d⁻¹|^2 • ∫ x, F x ∂(volume.prod volume)
  rw [integral_prod _ h₂, integral_prod _ h₁]
  have h (u : ℝ) : (∫ v, (F ∘ planeAffine a d hd) (u,v)) =
      |d⁻¹| • ∫ v, F (d*u+a.1,v) := by
    change (∫ v : ℝ, F (d*u+a.1,d*v+a.2)) = _
    rw [Measure.integral_comp_mul_left (fun v : ℝ => F (d*u+a.1,v+a.2)),
      integral_add_right_eq_self (fun v : ℝ => F (d*u+a.1,v))]
  simp_rw [h]
  rw [integral_smul, Measure.integral_comp_mul_left (fun u : ℝ => ∫ v, F (u+a.1,v)),
    integral_add_right_eq_self (fun u : ℝ => ∫ v, F (u,v)), smul_smul, pow_two]

theorem planeProduct_rescale {Φ : ℝ × ℝ → ℂ} {A B C : ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (hA : Continuous A)
    (hB : Continuous B) (hC : Continuous C) (a : ℝ × ℝ) {d : ℝ} (hd : d ≠ 0) :
    (∫ x : ℝ × ℝ, Φ x * (A (d*x.1+a.1) * B (d*x.2+a.2) * C (-(d*x.1+a.1+(d*x.2+a.2))))) =
    |d⁻¹|^2 • planeProduct (Φ ∘ (planeAffine a d hd).symm) A B C := by
  let P := planeAffine a d hd
  let F (x : ℝ × ℝ) := (Φ ∘ P.symm) x * (A x.1 * B x.2 * C (-(x.1+x.2)))
  have hP : Continuous (Φ ∘ P.symm) := hΦ.comp P.symm.continuous
  have hPc : HasCompactSupport (Φ ∘ P.symm) := hΦc.comp_homeomorph P.symm
  have hF : Continuous F := by unfold F; fun_prop
  calc
    _ = ∫ x, F (P x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [F, Function.comp_apply, Homeomorph.symm_apply_apply]
      rfl
    _ = _ := planeAffine_integral hF (hPc.mul_right : HasCompactSupport F) a hd

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.planeProduct_bound
#print axioms XiPrime8845.RHTriple.planeProduct_rescale
