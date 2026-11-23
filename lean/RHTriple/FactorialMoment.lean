/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.DistinctTripleMain
import RHTriple.SlotBlocks
import RHTriple.CertificateSmoothingInverse

/-! Sharp factorial counts and their comparison with the positive
smoothed, distinct-label three-point sum. -/

noncomputable section
open Complex MeasureTheory Finset

namespace XiPrime8845.RHTriple
open Zeta23 CertificateSmoothing

def thirdFalling (m : ℕ) : ℕ := m*(m-1)*(m-2)

def zetaM3 (A B : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ Zeta23.zerosIn A B, thirdFalling (zeroMult ρ)

theorem thirdFalling_cast (m : ℕ) :
    (thirdFalling m : ℝ) = (m:ℝ)*(m-1)*(m-2) := by
  by_cases hm : 2 ≤ m
  · simp [thirdFalling,Nat.cast_sub hm,Nat.cast_sub (show 1 ≤ m by omega)]
  · interval_cases m <;> norm_num [thirdFalling]

theorem three_mul_sub_one_le_thirdFalling {m : ℕ} (hm : 3 ≤ m) :
    3*(m-1) ≤ thirdFalling m := by
  unfold thirdFalling
  have h₀ : 3 ≤ m*(m-2) := by
    simpa using Nat.mul_le_mul hm (show 1 ≤ m-2 by omega)
  convert Nat.mul_le_mul_right (m-1) h₀ using 1
  ring

theorem zetaM3_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    zetaM3 a c = zetaM3 a b+zetaM3 b c := by
  have hdis : Disjoint (Zeta23.zerosIn a b) (Zeta23.zerosIn b c) := by
    rw [Set.disjoint_left]
    exact fun _ h h' => not_lt_of_ge h.2.2 h'.2.1
  have heq : Zeta23.zerosIn a b ∪ Zeta23.zerosIn b c = Zeta23.zerosIn a c := by
    ext ρ
    constructor
    · rintro (h|h)
      · exact ⟨h.1,h.2.1,h.2.2.trans hbc⟩
      · exact ⟨h.1,hab.trans_lt h.2.1,h.2.2⟩
    · intro h
      by_cases hi : ρ.im ≤ b
      · exact Or.inl ⟨h.1,h.2.1,hi⟩
      · exact Or.inr ⟨h.1,lt_of_not_ge hi,h.2.2⟩
  unfold zetaM3
  rw [← heq, finsum_mem_union hdis (zetaZeroConfig.window_finite _ _)
    (zetaZeroConfig.window_finite _ _)]

private theorem slotHeight_eq_physical (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    {h : ℝ → ℝ} (hh : ∀ t : ℝ, paperFT k t = (h t:ℂ)) {T : ℝ} (hT : 0 < T)
    (s : ZetaSlot) : slotHeight k T s = (h (slotOrdinate s/T):ℂ) := by
  have hg : gammaOf (s.1 : ℂ) = ((s.1 : ℂ).im : ℂ) := by
    apply Complex.ext
    · simp [WeilEF.gammaOf_re]
    · simp [WeilEF.gammaOf_im,RH_implies_on_line hRH s.1.property]
  rw [slotHeight,paperFT_dilate _ hT,hg,← Complex.ofReal_div,hh]
  rfl

theorem zetaM3_le_smoothedDistinctTriple (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {Φ : ℝ × ℝ → ℂ} {g : ℝ × ℝ → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g (0,0) = 1)
    {h : ℝ → ℝ} (hh : ∀ t : ℝ, paperFT k t = (h t:ℂ)) (hhn : ∀ t, 0 ≤ h t)
    (hh1 : ∀ t ∈ Set.Icc (1:ℝ) 2, 1 ≤ h t)
    {T : ℝ} (hT : 0 < T) :
    (zetaM3 T (2*T):ℝ) ≤ (smoothedDistinctTriple k Φ T).re := by
  classical
  let S := Zeta23.zerosIn T (2*T)
  have hS : S.Finite := zetaZeroConfig.window_finite _ _
  letI : Fintype S := hS.fintype
  let m (s : S) := zeroMult s.val
  let γ (s : S) := s.val.im
  let w (s : S) := h (γ s/T)
  let d := Real.log T/(2*Real.pi)
  have hγ : Function.Injective γ := by
    intro a b hab
    apply Subtype.ext
    apply Complex.ext
    · exact (RH_implies_on_line hRH a.property.1).trans
        (RH_implies_on_line hRH b.property.1).symm
    · exact hab
  let E : S ↪ ZetaZero := ⟨fun p => ⟨p.val,p.property.1⟩,fun _ _ e =>
    Subtype.ext (congrArg (fun ρ : ZetaZero => (ρ:ℂ)) e)⟩
  let e : (Σ s : S, Fin (m s)) ↪ ZetaSlot :=
    E.sigmaMap (fun s => Function.Embedding.refl _)
  let em := (e.prodMap e).prodMap e
  let F (r : (ZetaSlot×ZetaSlot)×ZetaSlot) : ℂ :=
    if distinctSlots r.1.1 r.1.2 r.2 then slotTripleSummand k Φ T r else 0
  have eF (r : (ZetaSlot×ZetaSlot)×ZetaSlot) :
      slotTripleSummand k Φ T r =
        (slotTest (fun s => slotOrdinate s/T) (fun s => h (slotOrdinate s/T)) g (d*T)
          r.1.1 r.1.2 r.2:ℂ) := by
    rw [slotTripleSummand,← planeInverse_triple_coordinates Φ (Real.log T),hg]
    unfold tripleWeight slotTest
    rw [slotHeight_eq_physical hRH hh hT,slotHeight_eq_physical hRH hh hT,
      slotHeight_eq_physical hRH hh hT]
    have e₁ (x y : ℝ) : d*T*(x/T-y/T) = d*(x-y) := by field_simp
    simp only [e₁, ofReal_mul,d]
  have hFn (r : (ZetaSlot×ZetaSlot)×ZetaSlot) : 0 ≤ (F r).re := by
    unfold F
    split
    · rw [eF,ofReal_re]
      exact mul_nonneg (mul_nonneg (mul_nonneg (hhn _) (hhn _)) (hhn _)) (hgn _)
    · simp
  have hFi : Summable F := (slotTriple_summable (Φ := Φ) hk hkc hT).of_norm_bounded
    fun r => by unfold F; split <;> simp
  have hreal : Summable (fun r => (F r).re) := Complex.reCLM.summable hFi
  have hw (s : S) : 1 ≤ w s := hh1 _ ⟨
    (le_div_iff₀ hT).2 (by simpa only [one_mul] using s.property.2.1.le),
    (div_le_iff₀ hT).2 s.property.2.2⟩
  have hm : (zetaM3 T (2*T):ℝ) ≤
      ∑ s : S, (m s:ℝ)*(m s-1)*(m s-2)*(w s)^3 := by
    unfold zetaM3
    rw [finsum_mem_eq_finite_toFinset_sum _ hS,Nat.cast_sum,← Finset.sum_attach]
    have hsum : (∑ x ∈ hS.toFinset.attach, (thirdFalling (zeroMult x.val):ℝ)) =
        ∑ s : S, (thirdFalling (m s):ℝ) := by
      apply Fintype.sum_equiv (Equiv.subtypeEquivRight (fun x => hS.mem_toFinset))
      intro p; rfl
    rw [hsum]
    apply sum_le_sum
    intro p _
    rw [← thirdFalling_cast]
    conv_lhs => rw [← mul_one (thirdFalling (m p):ℝ)]
    exact mul_le_mul_of_nonneg_left (one_le_pow₀ (hw p)) (Nat.cast_nonneg _)
  refine hm.trans ((factorialMoment_le_distinctSlots m γ w hγ g d
    (fun p => hhn _) hgn hg0).trans ?_)
  have heq : distinctSlotSum (univ : Finset (Σ s : S, Fin (m s)))
      (slotTest (γ ∘ Sigma.fst) (w ∘ Sigma.fst) g d) =
      ∑ r ∈ univ.map em, (F r).re := by
    rw [Finset.sum_map]
    unfold distinctSlotSum fullSlots
    simp only [Fintype.sum_prod_type]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro k _
    change (if distinctSlots i j k then
      slotTest (γ ∘ Sigma.fst) (w ∘ Sigma.fst) g d i j k else 0) = (F ((e i,e j),e k)).re
    have hse : distinctSlots (e i) (e j) (e k) ↔ distinctSlots i j k := by
      simp [distinctSlots,e.injective.eq_iff]
    by_cases hd : distinctSlots i j k
    · simp only [F, if_pos (hse.mpr hd), if_pos hd, eF, ofReal_re,Function.comp_apply]
      unfold slotTest
      have eqOrd (s : Σ s : S, Fin (m s)) : slotOrdinate (e s) = γ s.1 := rfl
      simp only [eqOrd]
      have H (x y : ℝ) : d*T*(x/T-y/T) = d*(x-y) := by field_simp
      simp only [H]
      rfl
    · simp [F,hd,show ¬distinctSlots (e i) (e j) (e k) from fun h => hd (hse.mp h)]
  rw [heq]
  have hlo := hreal.sum_le_tsum (univ.map em) (fun r _ => hFn r)
  have hhSum : (∑' r, (F r).re) = (smoothedDistinctTriple k Φ T).re :=
    (Complex.reCLM.map_tsum hFi).symm
  exact hlo.trans_eq hhSum

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.zetaM3_le_smoothedDistinctTriple
#print axioms XiPrime8845.RHTriple.zetaM3_add
#print axioms XiPrime8845.RHTriple.three_mul_sub_one_le_thirdFalling
