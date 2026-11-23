/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.ZetaSlotWeights
import RHTriple.CountableSlotSieve
import RHTriple.PairMarginalMain
import RHTriple.MixedGate

/-! Identify the four repeated-label strata of the whole-height
ζ three-slot sum with the mixed pair sums and the singleton. -/

noncomputable section
open Complex MeasureTheory

namespace XiPrime8845.RHTriple
open Zeta23

private theorem countable_roots : Countable ZetaZero := by
  apply Set.countable_coe_iff.mpr
  have heq : zetaZeroConfig.carrier = ⋃ n : ℕ, zetaZeroConfig.window (-(n : ℝ)) n := by
    ext ρ
    simp only [Set.mem_iUnion, ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hρ
      obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
      exact ⟨n, hρ, by linarith [neg_abs_le ρ.im], (le_abs_self _).trans hn.le⟩
    · rintro ⟨n, hρ, _, _⟩
      exact hρ
  rw [heq]
  exact Set.countable_iUnion fun n => (zetaZeroConfig.window_finite _ _).countable

def slotTripleSummand (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (T : ℝ)
    (r : (ZetaSlot × ZetaSlot) × ZetaSlot) : ℂ :=
  tripleWeight (slotHeight k T) r * (∫ p : ℝ × ℝ, Φ p *
    phase (differences (Real.log T) (slotOrdinate r.1.1) (slotOrdinate r.1.2) (slotOrdinate r.2) p))

def smoothedDistinctTriple (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ := by
  classical
  exact ∑' r : (ZetaSlot × ZetaSlot) × ZetaSlot,
    if distinctSlots r.1.1 r.1.2 r.2 then slotTripleSummand k Φ T r else 0

def slotCubeMass (k : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∑' ρ : ZetaZero, (zetaZeroConfig.mult ρ : ℂ) *
    (paperFT k ((ρ : ℂ).im / (T : ℂ)))^3

theorem slotTriple_summable {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T) :
    Summable fun r => ‖slotTripleSummand k Φ T r‖ := by
  have H := slotHeight_summable_norm hk hkc hT
  apply Summable.of_nonneg_of_le (fun r => norm_nonneg _)
    (f := fun r : (ZetaSlot × ZetaSlot) × ZetaSlot =>
      ‖tripleWeight (slotHeight k T) r‖ * ∫ p, ‖Φ p‖) ?_
    (((H.mul_norm H).mul_norm H).mul_right _)
  intro r
  rw [slotTripleSummand,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [norm_mul,norm_phase,mul_one]

private theorem slotTriple_unrestricted (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Integrable Φ) {T : ℝ} (hT : 0 < T) :
    (∑' r, slotTripleSummand k Φ T r) = smoothedTriple k Φ T := by
  let : Countable ZetaZero := countable_roots
  let L := Real.log T
  have H := integral_product Φ hΦ _ (slotHeight_summable_norm hk hkc hT) slotOrdinate L
  have hG := zeta_triple_explicit hRH (dilate_contDiff hk T) (dilate_hasCompactSupport hkc hT) Φ hΦ L
  simp_rw [zetaSlotPhase_eq_roots hk hkc hT,
    ← shifted_EF hRH (dilate_contDiff hk T) (dilate_hasCompactSupport hkc hT)] at H
  rw [hG] at H
  have h' : (∑' r, slotTripleSummand k Φ T r) =
      ∑' r, ∫ p : ℝ × ℝ, Φ p * (tripleWeight (slotHeight k T) r *
        phase (differences L (slotOrdinate r.1.1) (slotOrdinate r.1.2) (slotOrdinate r.2) p)) := by
    apply tsum_congr
    intro r
    unfold slotTripleSummand
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  rw [h', ← H]
  simp only [smoothedTriple,tripleWeight,heightWeight,paperFT_dilate _ hT,L]

private theorem mixedSlotPair_eq (hRH : RiemannHypothesis)
    {a b Q : ℝ → ℂ} (ha : ContDiff ℝ 2 a) (hca : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hcb : HasCompactSupport b) (hQ : Integrable Q) {T : ℝ} (hT : 0 < T) :
    (∑' p : ZetaSlot × ZetaSlot, slotHeight a T p.1 * slotHeight b T p.2 *
      lineTest Q (Real.log T*(slotOrdinate p.1-slotOrdinate p.2))) = smoothedPair a b Q T := by
  let : Countable ZetaZero := countable_roots
  rw [← pair_phase_integral hQ (slotHeight_summable_norm ha hca hT)
    (slotHeight_summable_norm hb hcb hT) slotOrdinate]
  simp_rw [zetaSlotPhase_eq_roots ha hca hT,zetaSlotPhase_eq_roots hb hcb hT,
    ← shifted_EF hRH (dilate_contDiff ha T) (dilate_hasCompactSupport hca hT),
    ← shifted_EF hRH (dilate_contDiff hb T) (dilate_hasCompactSupport hcb hT)]
  exact (smoothedPair_eq_integral_EF hRH ha hca hb hcb hQ hT).symm

theorem smoothedDistinctTriple_eq_sieve (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : ContDiff ℝ 1 Φ) (hcΦ : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η)
    {T : ℝ} (hT : 0 < T) :
    smoothedDistinctTriple k Φ T = smoothedTriple k Φ T -
      smoothedPair (heightSquareProfile k) k (marginalD Φ) T -
      smoothedPair k (heightSquareProfile k) (marginalY Φ) T -
      smoothedPair k (heightSquareProfile k) (marginalX Φ) T +
      2*((∫ p : ℝ × ℝ, Φ p)*slotCubeMass k T) := by
  classical
  obtain ⟨⟨hX,hcX⟩,⟨hY,hcY⟩,⟨hD,hcD⟩⟩ := marginals_contDiff_compact hΦ hη hhex
  let S := heightSquareProfile k
  have hS : ContDiff ℝ 2 S := heightSquareProfile_contDiff hk hkc
  have hcS : HasCompactSupport S := heightSquareProfile_compact hkc
  let L := Real.log T
  let a := slotHeight k T
  let γ := slotOrdinate
  let F := slotTripleSummand k Φ T
  have hsq (s : ZetaSlot) : slotHeight S T s = (a s)^2 :=
    slotHeight_square hRH hk hkc hT s
  have hψ (x : ℝ) : Continuous (fun u : ℝ => phase (u*x)) :=
    continuous_phase.comp (continuous_id.mul continuous_const)
  have hd : (∑' p : ZetaSlot × ZetaSlot, F ((p.1,p.1),p.2)) =
      smoothedPair S k (marginalD Φ) T := by
    rw [← mixedSlotPair_eq hRH hS hcS hk hkc (hD.continuous.integrable_of_hasCompactSupport hcD) hT]
    apply tsum_congr
    intro r
    have H (p : ℝ × ℝ) : differences L (γ r.1) (γ r.1) (γ r.2) p =
        (p.1+p.2)*(L*(γ r.1-γ r.2)) := by unfold differences; ring
    simp only [F,slotTripleSummand,tripleWeight,H,lineTest,hsq,pow_two,a,γ,L]
    rw [integral_marginalD hΦ.continuous hcΦ (hψ _)]
  have hy : (∑' p : ZetaSlot × ZetaSlot, F ((p.1,p.2),p.1)) =
      smoothedPair k S (marginalY Φ) T := by
    rw [← mixedSlotPair_eq hRH hk hkc hS hcS (hY.continuous.integrable_of_hasCompactSupport hcY) hT]
    rw [← (Equiv.prodComm ZetaSlot ZetaSlot).tsum_eq (fun p => F ((p.1,p.2),p.1))]
    apply tsum_congr
    intro r
    have H (p : ℝ × ℝ) : differences L (γ r.2) (γ r.1) (γ r.2) p =
        p.2*(L*(γ r.1-γ r.2)) := by unfold differences; ring
    simp only [Equiv.prodComm_apply,Prod.swap,F,slotTripleSummand,tripleWeight,H,lineTest,hsq,pow_two,a,γ,L]
    rw [integral_marginalY hΦ.continuous hcΦ (hψ _)]
    ring
  have hx : (∑' p : ZetaSlot × ZetaSlot, F ((p.1,p.2),p.2)) =
      smoothedPair k S (marginalX Φ) T := by
    rw [← mixedSlotPair_eq hRH hk hkc hS hcS (hX.continuous.integrable_of_hasCompactSupport hcX) hT]
    apply tsum_congr
    intro r
    have H (p : ℝ × ℝ) : differences L (γ r.1) (γ r.2) (γ r.2) p =
        p.1*(L*(γ r.1-γ r.2)) := by unfold differences; ring
    simp only [F,slotTripleSummand,tripleWeight,H,lineTest,hsq,pow_two,a,γ,L]
    rw [integral_marginalX hΦ.continuous hcΦ (hψ _)]
    ring
  have hE (s : ZetaSlot) : a s = paperFT k ((γ s:ℂ)/(T:ℂ)) := by
    have hg : gammaOf (s.1 : ℂ) = ((s.1 : ℂ).im : ℂ) := by
      apply Complex.ext
      · simp [WeilEF.gammaOf_re]
      · simp [WeilEF.gammaOf_im,RH_implies_on_line hRH s.1.property]
    simp only [a,γ,slotHeight,slotOrdinate,paperFT_dilate _ hT,hg]
  have hcube : Summable (fun s : ZetaSlot => (a s)^3) := by
    have H := slotHeight_summable_norm hk hkc hT
    let M := ∑' s : ZetaSlot, ‖a s‖
    apply (H.mul_right (M^2)).of_norm_bounded
    intro s
    rw [norm_pow,pow_succ' _ 2]
    have hB : ‖a s‖ ≤ M := H.le_tsum s (fun _ _ => norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hB _) (norm_nonneg _)
  have ho : (∑' s : ZetaSlot, F ((s,s),s)) = (∫ p : ℝ × ℝ, Φ p)*slotCubeMass k T := by
    have he (s : ZetaSlot) : F ((s,s),s) = (∫ p : ℝ × ℝ, Φ p)*(a s)^3 := by
      simp [F,slotTripleSummand,tripleWeight,differences,phase,a,pow_succ, mul_comm]
    simp_rw [he,tsum_mul_left]
    congr 1
    rw [hcube.tsum_sigma' (fun _ => hasSum_fintype _ |>.summable)]
    simp only [tsum_fintype,hE,γ,slotOrdinate,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,slotCubeMass]
  unfold smoothedDistinctTriple
  rw [distinctSlotTsum_eq F (slotTriple_summable hk hkc hT),
    slotTriple_unrestricted hRH hk hkc (hΦ.continuous.integrable_of_hasCompactSupport hcΦ) hT,
    hd,hy,hx,ho]

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.smoothedDistinctTriple_eq_sieve
