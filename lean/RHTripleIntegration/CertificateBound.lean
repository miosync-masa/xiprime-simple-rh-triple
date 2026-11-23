/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.FactorialCertificate
import RHBridge.MultiplicityBridge

/-! Optional three-branch integration target. The triple and multiplicity
worktrees are independent; compile this with both module roots available.
The numerical certificate and convergence of its normalized Fourier tests
are explicit inputs until the certificate branch is linked. -/

noncomputable section
open Filter Topology MeasureTheory

namespace XiPrime8845.RHTripleIntegration
open XiPrime8845.RHTriple XiPrime8845.RHTriple.CertificateSmoothing XiPrime8845.RHBridge
open Zeta23

theorem three_mul_highZeros_le_zetaM3 (A B : ℝ) :
    3*(∑ᶠ ρ ∈ highZeros A B, (zeroMult ρ-1)) ≤ zetaM3 A B := by
  classical
  have hs : highZeros A B ⊆ Zeta23.zerosIn A B := fun _ h => h.1
  have hF : (Zeta23.zerosIn A B).Finite := zetaZeroConfig.window_finite A B
  have hH := hF.subset hs
  unfold zetaM3
  rw [finsum_mem_eq_finite_toFinset_sum _ hH,finsum_mem_eq_finite_toFinset_sum _ hF,
    Finset.mul_sum]
  have hsub : hH.toFinset ⊆ hF.toFinset := by
    intro x hx
    exact hF.mem_toFinset.mpr (hs (hH.mem_toFinset.mp hx))
  calc
    _ ≤ ∑ ρ ∈ hH.toFinset, thirdFalling (zeroMult ρ) :=
      Finset.sum_le_sum (fun ρ hρ => three_mul_sub_one_le_thirdFalling (hH.mem_toFinset.mp hρ).2)
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

theorem simple_dyadic_of_factorial_bound (hRH : RiemannHypothesis)
    {c₂₀ : ℝ} (hc : 0 ≤ c₂₀) (h : DyadicM3Upper c₂₀) :
    ∀ e > 0, ∀ᶠ T in atTop,
      (1-c₂₀/3-e)*(XiPrime.Ncount T (2*T):ℝ) ≤ (XiPrime.N0simple T (2*T):ℝ) := by
  intro e he
  have h3 : ∀ᶠ T in atTop, ((∑ᶠ ρ ∈ highZeros T (2*T), (zeroMult ρ-1) : ℕ):ℝ) ≤
        ((c₂₀+e)/3)*(Zeta23.Ncount T (2*T):ℝ) := by
    filter_upwards [h e he] with T hT
    have H : 3*((∑ᶠ ρ ∈ highZeros T (2*T), (zeroMult ρ-1) : ℕ):ℝ) ≤ (zetaM3 T (2*T):ℝ) := by
      exact_mod_cast three_mul_highZeros_le_zetaM3 T (2*T)
    linarith only [H,hT]
  have H := simple_proportion_of_highZeros_bound hRH
    (c := (c₂₀+e)/3) (by positivity) h3 (2*e/3) (by positivity)
  convert H using 3
  ring

theorem simple_liminf_of_factorial_bound (hRH : RiemannHypothesis)
    {c₂₀ : ℝ} (hc : 0 ≤ c₂₀) (h : DyadicM3Upper c₂₀) :
    1-c₂₀/3 ≤ liminf
      (fun T => (XiPrime.N0simple 0 T:ℝ)/(XiPrime.Ncount 0 T:ℝ)) atTop := by
  let F := XiPrime.xiDerivZerosInStrip_holds
  let S := XiPrime.xiDerivSeam_of_strip F
  let Z := XiPrime.xiDerivZeros F S
  let R := XiPrime.xiDeriv_riemannVonMangoldt F S
  have hd := simple_dyadic_of_factorial_bound hRH hc h
  have hN' := (Assembly.tendsto_N_atTop Z R).comp
    (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
  have hN : Tendsto (fun T => (XiPrime.Ncount 0 T:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' _ ?_ hN'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    change (Z.N (T/2) (2*(T/2)):ℝ) ≤ (XiPrime.Ncount 0 T:ℝ)
    have eq : Z.N 0 T = Z.N 0 (T/2) + Z.N (T/2) T :=
      Assembly.N_add Z (by linarith) (by linarith)
    change _ ≤ (Z.N 0 T:ℝ)
    rw [show 2*(T/2)=T by ring,eq,Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) (Z.N 0 (T/2))]
  have H := Assembly.dyadic (f := fun a b => (XiPrime.N0simple a b:ℝ))
    (g := fun a b => (XiPrime.Ncount a b:ℝ)) (c := 1-c₂₀/3)
    (fun a b d hab hbd => by exact_mod_cast (Assembly.N0s_add Z hab hbd :
      XiPrime.N0simple a d = XiPrime.N0simple a b+XiPrime.N0simple b d))
    (fun a b d hab hbd => by exact_mod_cast (Assembly.N_add Z hab hbd :
      XiPrime.Ncount a d = XiPrime.Ncount a b+XiPrime.Ncount b d))
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _) hN
    (fun e he => eventually_atTop.mp (hd e he))
  have hb : IsCoboundedUnder (· ≥ ·) atTop
      (fun T => (XiPrime.N0simple 0 T:ℝ)/(XiPrime.Ncount 0 T:ℝ)) := by
    apply isCoboundedUnder_ge_of_eventually_le (x := 1) atTop
    filter_upwards [hN.eventually_gt_atTop 0] with T hT
    apply (div_le_iff₀ hT).2
    rw [one_mul]
    have C := Z.trivial_chain 0 T
    exact_mod_cast C.1.trans (C.2.1.trans C.2.2.1)
  have hl (e : ℝ) (he : 0 < e) : 1-c₂₀/3-e ≤ liminf
      (fun T => (XiPrime.N0simple 0 T:ℝ)/(XiPrime.Ncount 0 T:ℝ)) atTop := by
    apply le_liminf_of_le hb
    filter_upwards [eventually_atTop.mpr (H e he), hN.eventually_gt_atTop 0] with T hT hp
    exact (le_div_iff₀ hp).2 hT
  apply le_of_forall_pos_le_add
  intro e he
  linarith only [hl e he]

theorem simple_liminf_of_certificate (hRH : RiemannHypothesis)
    {Φ : Plane → ℂ} (hΦ : Integrable Φ) (hcΦ : HasCompactSupport Φ)
    (hhex : ∀ p, Φ p ≠ 0 → hexGauge p ≤ 2)
    {g : Plane → ℝ} (hg : ∀ p, planeInverse Φ p = (g p:ℂ))
    (hgn : ∀ p, 0 ≤ g p) (hg0 : g 0 = 1)
    {l : Filter InteriorEpsilon} [l.NeBot]
    (hlim : Tendsto (fun e => (nu3F (smoothedCertificate Φ e) /
      nu3Mass (smoothedCertificate Φ e)).re) l (𝓝 ((nu3F Φ/nu3Mass Φ).re)))
    {c₂₀ : ℝ} (hc : 0 ≤ c₂₀) (hnum : (nu3F Φ/nu3Mass Φ).re ≤ c₂₀) :
    1-c₂₀/3 ≤ liminf
      (fun T => (XiPrime.N0simple 0 T:ℝ)/(XiPrime.Ncount 0 T:ℝ)) atTop :=
  simple_liminf_of_factorial_bound hRH hc
    (zetaM3_dyadic_of_certificate_limit hRH hΦ hcΦ hhex hg hgn hg0 hlim hnum)

end XiPrime8845.RHTripleIntegration

#print axioms XiPrime8845.RHTripleIntegration.three_mul_highZeros_le_zetaM3
#print axioms XiPrime8845.RHTripleIntegration.simple_dyadic_of_factorial_bound
#print axioms XiPrime8845.RHTripleIntegration.simple_liminf_of_factorial_bound
#print axioms XiPrime8845.RHTripleIntegration.simple_liminf_of_certificate
