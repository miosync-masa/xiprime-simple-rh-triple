/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
Portions adapted from the Anthropic AF library (Zeta23, formal-math commit
3635e74826a4c1fcece7d1cd2b6fa75e43a00510), Copyright (c) 2026 Anthropic, PBC, Apache-2.0:
the proof of `eventually_zetaCount_le` mirrors `eventually_zetaCount_le_Ncount`
(Zeta23/XiPrime/Final.lean). See RHBridge/README.md.
-/
import Zeta23.XiPrime.ExplicitFormula.ZeroFree
import Zeta23.XiPrime.Seam
import Zeta23.Statement.SeamClosed
import Zeta23.XiPrime.ZeroCount

/-! # The multiplicity bridge under RH

`hRH : RiemannHypothesis` (Mathlib's statement) is an explicit argument of every
theorem below that uses it; nothing here proves or assumes it globally.

Under RH, with `s` a zero of ξ′:
* if ξ(s) ≠ 0 then `Re s = 1/2` (sign of `Re ξ′/ξ`) and the zero is simple
  (`Re ξ′/ξ(s+ε) ≥ ε/D` to the right of the line, against `O(ε²)` at a multiple zero);
* if ξ(s) = 0 then `s` is a nontrivial zero of ζ of multiplicity `m` and
  ξ′ vanishes there to order `m - 1`.

Hence the exact count `Ncount_eq`:
`N_{ξ′}(T₁,T₂) = N⁰ˢ_{ξ′}(T₁,T₂) + ∑_{ρ : m_ρ ≥ 3} (m_ρ - 1)`.

Branch-only file (`rh-multiplicity-bridge`); not part of v1.0.0 or its SHA256SUMS. -/

open scoped BigOperators ComplexConjugate
open Complex Set Filter Topology
open Zeta23
open Zeta23.XiPrime (xi xiDeriv xiDerivMult IsXiDerivZero)

noncomputable section
namespace XiPrime8845.RHBridge

/-- To the right of (or on) the line, one zero already bounds `Re ξ′/ξ` from below. -/
theorem re_logDeriv_ge (hRH : RiemannHypothesis) {s ρ₀ : ℂ} (hρ₀ : IsNontrivialZero ρ₀)
    (hs : 1 / 2 ≤ s.re) (hxi : xi s ≠ 0) :
    (s.re - 1 / 2) / Complex.normSq (s - ρ₀) ≤ (logDeriv xi s).re := by
  rw [XiPrime.ZeroFree.re_logDeriv_xi_eq_tsum hxi]
  have hsum := XiPrime.ZeroFree.summable_re_one_div hxi
  have hnn : ∀ ρ : zetaZeroConfig.carrier,
      0 ≤ (zeroMult ρ : ℝ) * ((s.re - (ρ : ℂ).re) / Complex.normSq (s - ρ)) := by
    intro ρ
    have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
    have hre := RH_implies_on_line hRH hρ
    have h0 : 0 ≤ s.re - (ρ : ℂ).re := by rw [hre]; linarith
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg h0 (Complex.normSq_nonneg _))
  have hle := hsum.le_tsum (⟨ρ₀, hρ₀⟩ : zetaZeroConfig.carrier) (fun j _ => hnn j)
  refine le_trans ?_ hle
  have hm : (1 : ℝ) ≤ zeroMult ρ₀ := by exact_mod_cast zetaSeam.one_le_mult ρ₀ hρ₀
  have hre := RH_implies_on_line hRH hρ₀
  have hq : 0 ≤ (s.re - 1 / 2) / Complex.normSq (s - ρ₀) :=
    div_nonneg (by linarith) (Complex.normSq_nonneg _)
  show _ ≤ (zeroMult ρ₀ : ℝ) * ((s.re - ρ₀.re) / Complex.normSq (s - ρ₀))
  rw [hre]
  nlinarith

private lemma logDeriv_eq_zero {z : ℂ} (hz : xiDeriv z = 0) : logDeriv xi z = 0 := by
  have : deriv xi z = 0 := hz
  simp [logDeriv_apply, this]

private lemma not_right (hRH : RiemannHypothesis) {z : ℂ} (hz : xiDeriv z = 0)
    (hxz : xi z ≠ 0) : ¬ (1 / 2 < z.re) := by
  intro hlt
  obtain ⟨ρ₀, hρ₀⟩ := XiPrime.ZeroFree.exists_isNontrivialZero
  have h1 := re_logDeriv_ge hRH hρ₀ hlt.le hxz
  rw [logDeriv_eq_zero hz, Complex.zero_re] at h1
  have hne : z ≠ ρ₀ := fun h => hxz (h ▸ (XiPrime.ZeroFree.xi_eq_zero_iff ρ₀).mpr hρ₀)
  have hpos : 0 < Complex.normSq (z - ρ₀) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have : 0 < (z.re - 1 / 2) / Complex.normSq (z - ρ₀) := div_pos (by linarith) hpos
  linarith

/-- **Under RH, a zero of ξ′ that is not a zero of ξ lies on the critical line.** -/
theorem re_eq_half_of_xiDeriv_eq_zero (hRH : RiemannHypothesis) {s : ℂ}
    (hd : xiDeriv s = 0) (hxi : xi s ≠ 0) : s.re = 1 / 2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hz : xiDeriv (1 - s) = 0 := by rw [XiPrime.xiDeriv_one_sub, hd, neg_zero]
    have hxz : xi (1 - s) ≠ 0 := by rw [XiPrime.xi_one_sub]; exact hxi
    refine not_right hRH hz hxz ?_
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  · exact not_right hRH hd hxi h

/-- **Under RH, a zero of ξ′ that is not a zero of ξ is simple.** -/
theorem xiDerivMult_eq_one (hRH : RiemannHypothesis) {s : ℂ}
    (hd : xiDeriv s = 0) (hxi : xi s ≠ 0) : xiDerivMult s = 1 := by
  have hre := re_eq_half_of_xiDeriv_eq_zero hRH hd hxi
  have h1 : 1 ≤ xiDerivMult s := (XiPrime.one_le_xiDerivMult_iff s).mpr hd
  by_contra hne
  have h2 : 2 ≤ xiDerivMult s := by omega
  have h2' : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt xiDeriv s := by
    rw [← XiPrime.xiDerivMult_cast]
    exact_mod_cast h2
  obtain ⟨g, hg, hev⟩ := (natCast_le_analyticOrderAt (XiPrime.xiDeriv_analyticAt s)).mp h2'
  obtain ⟨ρ₀, hρ₀⟩ := XiPrime.ZeroFree.exists_isNontrivialZero
  have hρre := RH_implies_on_line hRH hρ₀
  have hxc : ContinuousAt xi s := XiPrime.xi_differentiable.continuous.continuousAt
  have hqc : ContinuousAt (fun z => g z / xi z) s := hg.continuousAt.div hxc hxi
  have hb : ∀ᶠ z in 𝓝 s, ‖g z / xi z‖ < ‖g s / xi s‖ + 1 :=
    (hqc.norm : Tendsto _ _ _).eventually (gt_mem_nhds (lt_add_one _))
  have hx0 : ∀ᶠ z in 𝓝 s, xi z ≠ 0 := hxc.eventually_ne hxi
  set C : ℝ := ‖g s / xi s‖ + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and (hb.and hx0))
  set D : ℝ := 1 + (s.im - ρ₀.im) ^ 2 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  set ε : ℝ := min (δ / 2) (min 1 (1 / (2 * C * D))) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεC : ε * (2 * C * D) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  set z : ℂ := s + (ε : ℂ) with hz
  have hzs : z - s = (ε : ℂ) := by rw [hz]; ring
  have hdist : dist z s < δ := by
    rw [dist_eq_norm, hzs, Complex.norm_real, Real.norm_of_nonneg hε0.le]; exact hεδ
  obtain ⟨hz1, hz2, hz3⟩ := hball hdist
  have hl : logDeriv xi z = (ε : ℂ) ^ 2 * (g z / xi z) := by
    have hdz : deriv xi z = (z - s) ^ 2 • g z := hz1
    rw [logDeriv_apply, hdz, hzs, smul_eq_mul, mul_div_assoc]
  have hup : (logDeriv xi z).re ≤ ε ^ 2 * C := by
    calc (logDeriv xi z).re ≤ ‖logDeriv xi z‖ := Complex.re_le_norm _
      _ = ε ^ 2 * ‖g z / xi z‖ := by
          rw [hl, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hε0.le]
      _ ≤ ε ^ 2 * C := mul_le_mul_of_nonneg_left hz2.le (by positivity)
  have hzre : z.re = 1 / 2 + ε := by rw [hz]; simp [hre]
  have hzim : z.im = s.im := by rw [hz]; simp
  have hlow := re_logDeriv_ge hRH hρ₀ (by rw [hzre]; linarith) hz3
  have hne : z ≠ ρ₀ := fun h => hz3 (h ▸ (XiPrime.ZeroFree.xi_eq_zero_iff ρ₀).mpr hρ₀)
  have hnsp : 0 < Complex.normSq (z - ρ₀) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have hns : Complex.normSq (z - ρ₀) ≤ D := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hzre, hzim, hρre, hD]
    nlinarith
  have hstep : ε / D ≤ (z.re - 1 / 2) / Complex.normSq (z - ρ₀) := by
    rw [hzre, add_sub_cancel_left]
    exact div_le_div_of_nonneg_left hε0.le hnsp hns
  have hfin : ε / D ≤ ε ^ 2 * C := by linarith
  rw [div_le_iff₀ hDpos] at hfin
  have hmul : ε * (ε * (2 * C * D)) ≤ ε * 1 := mul_le_mul_of_nonneg_left hεC hε0.le
  nlinarith

/-- At a nontrivial zero of ζ of multiplicity `m`, ξ′ vanishes to order `m - 1`
(no RH needed). -/
theorem xiDerivMult_add_one {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    xiDerivMult ρ + 1 = zeroMult ρ := by
  have hxi : xi ρ = 0 := (XiPrime.ZeroFree.xi_eq_zero_iff ρ).mpr hρ
  have h := (XiPrime.xi_analyticAt ρ).analyticOrderAt_deriv_add_one
  simp only [hxi, sub_zero] at h
  have h' : analyticOrderAt xiDeriv ρ + 1 = analyticOrderAt xi ρ := h
  rw [← XiPrime.ZeroFree.analyticOrderNatAt_xi hρ]
  unfold analyticOrderNatAt
  rw [← h', ← XiPrime.xiDerivMult_cast]
  rfl

/-- Nontrivial zeros of ζ in the window with multiplicity at least three. -/
def highZeros (T₁ T₂ : ℝ) : Set ℂ := {ρ | ρ ∈ Zeta23.zerosIn T₁ T₂ ∧ 3 ≤ zeroMult ρ}

/-- **The multiplicity bridge.** Under RH, the zeros of ξ′ in a height window, counted
with multiplicity, are the simple on-line zeros plus `m - 1` for each zero of ζ of
multiplicity `m ≥ 3`. -/
theorem Ncount_eq (hRH : RiemannHypothesis) (T₁ T₂ : ℝ) :
    XiPrime.Ncount T₁ T₂ =
      XiPrime.N0simple T₁ T₂ + ∑ᶠ ρ ∈ highZeros T₁ T₂, (zeroMult ρ - 1) := by
  set A := XiPrime.zerosIn T₁ T₂ with hA
  set S := A ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | xiDerivMult ρ = 1} with hS
  have hAfin : A.Finite := by
    have h := (XiPrime.xiDerivSeam_of_strip XiPrime.xiDerivZerosInStrip_holds).finite_window T₁ T₂
    exact h.subset (fun ρ hρ => ⟨hρ.1, hρ.2⟩)
  have hsplit : S ∪ highZeros T₁ T₂ = A := by
    ext ρ
    constructor
    · rintro (h | h)
      · exact h.1.1
      · have hm := xiDerivMult_add_one h.1.1
        have h3 : 3 ≤ zeroMult ρ := h.2
        exact ⟨(XiPrime.one_le_xiDerivMult_iff ρ).mp (by omega), h.1.2⟩
    · intro hρ
      by_cases hxi : xi ρ = 0
      · have hnt := (XiPrime.ZeroFree.xi_eq_zero_iff ρ).mp hxi
        have hm := xiDerivMult_add_one hnt
        by_cases h1 : xiDerivMult ρ = 1
        · exact Or.inl ⟨⟨hρ, RH_implies_on_line hRH hnt⟩, h1⟩
        · have h1' := (XiPrime.one_le_xiDerivMult_iff ρ).mpr hρ.1
          exact Or.inr ⟨⟨hnt, hρ.2⟩, by omega⟩
      · exact Or.inl ⟨⟨hρ, re_eq_half_of_xiDeriv_eq_zero hRH hρ.1 hxi⟩,
          xiDerivMult_eq_one hRH hρ.1 hxi⟩
  have hdisj : Disjoint S (highZeros T₁ T₂) := by
    rw [Set.disjoint_left]
    intro ρ hρS hρH
    have hm := xiDerivMult_add_one hρH.1.1
    have h1 : xiDerivMult ρ = 1 := hρS.2
    have h3 : 3 ≤ zeroMult ρ := hρH.2
    omega
  have hSfin : S.Finite := hAfin.subset (fun ρ h => h.1.1)
  have hHfin : (highZeros T₁ T₂).Finite :=
    hAfin.subset (fun ρ h => by rw [← hsplit]; exact Or.inr h)
  have e : XiPrime.Ncount T₁ T₂ = ∑ᶠ ρ ∈ S ∪ highZeros T₁ T₂, xiDerivMult ρ := by
    rw [hsplit]; rfl
  rw [e, finsum_mem_union hdisj hSfin hHfin]
  congr 1
  · have h1 : ∑ᶠ ρ ∈ S, xiDerivMult ρ = ∑ᶠ ρ ∈ S, 1 :=
      finsum_mem_congr rfl (fun ρ hρ => hρ.2)
    rw [h1, finsum_mem_eq_finite_toFinset_sum _ hSfin, Finset.sum_const, smul_eq_mul, mul_one]
    exact (Set.ncard_eq_toFinset_card S hSfin).symm
  · exact finsum_mem_congr rfl (fun ρ hρ => by
      have := xiDerivMult_add_one hρ.1.1
      omega)

/-- Inequality form: the non-simple zeros of ξ′ (with multiplicity) are bounded by the
`m - 1` sum over zeros of ζ of multiplicity at least three. -/
theorem Ncount_sub_N0simple_le (hRH : RiemannHypothesis) (T₁ T₂ : ℝ) :
    XiPrime.Ncount T₁ T₂ - XiPrime.N0simple T₁ T₂ ≤
      ∑ᶠ ρ ∈ highZeros T₁ T₂, (zeroMult ρ - 1) := by
  rw [Ncount_eq hRH T₁ T₂]; omega

/-! ## Denominators: N_ζ against N_{ξ′}

Both configurations satisfy Riemann–von Mangoldt with the same main term (AF:
`Zeta23.RvM.riemannVonMangoldt`, `XiPrime.xiDeriv_riemannVonMangoldt`). The proof below
mirrors AF's `eventually_zetaCount_le_Ncount` (XiPrime/Final.lean, Apache-2.0; see RHBridge/README.md)
in the opposite direction. No RH is used in the comparison itself. -/

open Asymptotics in
/-- `N_ζ(T,2T) ≤ (1+δ)·N_{ξ′}(T,2T)` eventually, for every `δ > 0`. Unconditional. -/
theorem eventually_zetaCount_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ T in atTop, (Zeta23.Ncount T (2 * T) : ℝ) ≤ (1 + δ) * (XiPrime.Ncount T (2 * T) : ℝ) := by
  set Zx := XiPrime.xiDerivZeros XiPrime.xiDerivZerosInStrip_holds
    (XiPrime.xiDerivSeam_of_strip XiPrime.xiDerivZerosInStrip_holds) with hZx
  have hRx : RiemannVonMangoldt Zx := XiPrime.xiDeriv_riemannVonMangoldt _ _
  have hRζ : RiemannVonMangoldt zetaZeroConfig := Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  obtain ⟨C₁, T₁, h₁⟩ := hRx.main
  obtain ⟨C₂, T₂, h₂⟩ := hRζ.main
  have ho : (fun T => (|C₁| + |C₂|) * Real.log T) =o[atTop] fun T => (Zx.N T (2 * T) : ℝ) :=
    Assembly.isLittleO_N_of_isLittleO_Tl _ hRx (Assembly.isLittleO_log_Tl.const_mul_left _)
  filter_upwards [ho.def hδ, eventually_ge_atTop T₁, eventually_ge_atTop T₂,
    eventually_ge_atTop (1 : ℝ)] with T hsmall hT₁ hT₂ hT1
  have hN0 : 0 ≤ (Zx.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0, abs_of_nonneg (by positivity)] at hsmall
  have a₁ := (abs_le.mp (h₁ T hT₁)).1
  have a₂ := (abs_le.mp (h₂ T hT₂)).2
  have e : (Zx.N T (2 * T) : ℝ) = (XiPrime.Ncount T (2 * T) : ℝ) := by simp [hZx]
  have ez : (zetaZeroConfig.N T (2 * T) : ℝ) = (Zeta23.Ncount T (2 * T) : ℝ) := by simp
  rw [e] at a₁ hsmall
  rw [ez] at a₂
  have hC₁ : C₁ * Real.log T ≤ |C₁| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self _) hlog
  have hC₂ : C₂ * Real.log T ≤ |C₂| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self _) hlog
  linarith

/-- **Proportion form of the bridge.** Under RH: if the `m - 1` sum over zeros of ζ of
multiplicity at least three is eventually at most `c·N_ζ(T,2T)`, then for every `ε > 0`
eventually `(1 - c - ε)·N_{ξ′}(T,2T) ≤ N⁰ˢ_{ξ′}(T,2T)`. -/
theorem simple_proportion_of_highZeros_bound (hRH : RiemannHypothesis) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ᶠ T in atTop, ((∑ᶠ ρ ∈ highZeros T (2 * T), (zeroMult ρ - 1) : ℕ) : ℝ) ≤
      c * (Zeta23.Ncount T (2 * T) : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
      (1 - c - ε) * (XiPrime.Ncount T (2 * T) : ℝ) ≤ (XiPrime.N0simple T (2 * T) : ℝ) := by
  intro ε hε
  set δ : ℝ := ε / (c + 1) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hcd : c * δ ≤ ε := by
    rw [hδ, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  filter_upwards [h, eventually_zetaCount_le δ hδ0] with T hT hz
  have hNx : 0 ≤ (XiPrime.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have heq : (XiPrime.Ncount T (2 * T) : ℝ) = (XiPrime.N0simple T (2 * T) : ℝ) +
      ((∑ᶠ ρ ∈ highZeros T (2 * T), (zeroMult ρ - 1) : ℕ) : ℝ) := by
    exact_mod_cast Ncount_eq hRH T (2 * T)
  have hx := hT.trans (mul_le_mul_of_nonneg_left hz hc)
  have hm := mul_le_mul_of_nonneg_right hcd hNx
  nlinarith

end XiPrime8845.RHBridge

#print axioms XiPrime8845.RHBridge.re_logDeriv_ge
#print axioms XiPrime8845.RHBridge.re_eq_half_of_xiDeriv_eq_zero
#print axioms XiPrime8845.RHBridge.xiDerivMult_eq_one
#print axioms XiPrime8845.RHBridge.xiDerivMult_add_one
#print axioms XiPrime8845.RHBridge.Ncount_eq
#print axioms XiPrime8845.RHBridge.Ncount_sub_N0simple_le
#print axioms XiPrime8845.RHBridge.eventually_zetaCount_le
#print axioms XiPrime8845.RHBridge.simple_proportion_of_highZeros_bound
