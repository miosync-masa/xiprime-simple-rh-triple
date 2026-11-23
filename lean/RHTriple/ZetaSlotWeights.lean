/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.PairIntegrated

/-! Split each ζ root into as many labelled copies as its AF
multiplicity. Height weights and their phase sums are unchanged when
the finite fibres are collected back into roots. -/

noncomputable section
open MeasureTheory

namespace XiPrime8845.RHTriple
open Zeta23

abbrev ZetaSlot := Σ ρ : ZetaZero, Fin (zetaZeroConfig.mult ρ)

def slotOrdinate (s : ZetaSlot) : ℝ := (s.1 : ℂ).im

def slotHeight (k : ℝ → ℂ) (T : ℝ) (s : ZetaSlot) : ℂ :=
  paperFT (dilate k T) (gammaOf s.1)

theorem slotHeight_summable_norm {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T) :
    Summable (fun s : ZetaSlot => ‖slotHeight k T s‖) := by
  apply (summable_sigma_of_nonneg (fun (_ : ZetaSlot) => norm_nonneg _)).2
  refine ⟨fun _ => hasSum_fintype _ |>.summable,?_⟩
  have root := heightWeight_summable_norm (dilate_contDiff hk T) (dilate_hasCompactSupport hkc hT)
  simpa only [tsum_fintype, slotHeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, heightWeight, norm_mul, Complex.norm_natCast] using root

theorem zetaSlotPhase_eq_roots {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    pairPhaseSum (slotHeight k T) slotOrdinate x =
      pairPhaseSum (heightWeight (dilate k T)) (fun ρ : ZetaZero => (ρ : ℂ).im) x := by
  let F (s : ZetaSlot) := slotHeight k T s * phase (slotOrdinate s*x)
  have hF : Summable F := (slotHeight_summable_norm hk hkc hT).of_norm_bounded (fun s => by
    simp only [F,norm_mul,norm_phase,mul_one,le_refl])
  unfold pairPhaseSum
  change (∑' s, F s) = _
  rw [hF.tsum_sigma' (fun _ => hasSum_fintype _ |>.summable)]
  simp only [tsum_fintype,F,slotHeight,slotOrdinate,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,heightWeight,mul_assoc]

theorem slotHeight_square (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T)
    (s : ZetaSlot) :
    slotHeight (heightSquareProfile k) T s = (slotHeight k T s)^2 := by
  have hg : gammaOf (s.1 : ℂ) = ((s.1 : ℂ).im : ℂ) := by
    apply Complex.ext
    · simp [WeilEF.gammaOf_re]
    · simp [WeilEF.gammaOf_im,RH_implies_on_line hRH s.1.property]
  unfold slotHeight
  rw [paperFT_dilate _ hT,paperFT_dilate _ hT,hg,← Complex.ofReal_div,
    paperFT_heightSquareProfile hk hkc]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.slotHeight_summable_norm
#print axioms XiPrime8845.RHTriple.zetaSlotPhase_eq_roots
#print axioms XiPrime8845.RHTriple.slotHeight_square
