/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.TripleMain
import RHTriple.PairMarginalMain

/-! Fourier-side inclusion–exclusion coefficient. This is the same
formula as XiPrime8845.Triple.Nu3.nu3F in the certificate worktree. -/
noncomputable section
open MeasureTheory
namespace XiPrime8845.RHTriple

def nu3Kernel (ξ : ℝ × ℝ) : ℝ := max 0 (1 - (|ξ.1| + |ξ.2| + |ξ.1 + ξ.2|) / 2)

def lineInt (Φ : ℝ × ℝ → ℂ) (ℓ : ℝ → ℝ × ℝ) : ℂ :=
  ∫ u in (-1 : ℝ)..1, ((1 - |u| : ℝ) : ℂ) * Φ (ℓ u)

def nu3F (Φ : ℝ × ℝ → ℂ) : ℂ :=
  Φ (0, 0) - (lineInt Φ (fun u => (u, -u)) + lineInt Φ (fun u => (u, 0))
    + lineInt Φ (fun u => (0, u))) + 2 * ∫ ξ : ℝ × ℝ, (nu3Kernel ξ : ℂ) * Φ ξ

def nu3Mass (Φ : ℝ × ℝ → ℂ) : ℂ := ∫ ξ : ℝ × ℝ, Φ ξ

private theorem splitAbs {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ t in (-1:ℝ)..1, ((|t| : ℝ) : ℂ)*F t) =
      (∫ t in (0:ℝ)..1, F (-t)*(t:ℂ)) + ∫ t in (0:ℝ)..1, F t*(t:ℂ) := by
  let f (t : ℝ) : ℂ := ((|t| : ℝ) : ℂ)*F t
  have hc : Continuous f := by unfold f; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)]
  congr 1
  · have hh := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1) f
    rw [neg_zero] at hh
    change (∫ t in (-1:ℝ)..0, f t) = _
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    simp [f, abs_of_nonneg hu.1, mul_comm]
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    simp [f, abs_of_nonneg hu.1, mul_comm]

private theorem lineDiff {Φ : ℝ × ℝ → ℂ} (ℓ : ℝ → ℝ × ℝ)
    (hF : Continuous (Φ ∘ ℓ)) (hzero : ∀ t ∉ Set.Ioc (-1:ℝ) 1, Φ (ℓ t) = 0) :
    (∫ t in (-1:ℝ)..1, ((|t| : ℝ) : ℂ)*Φ (ℓ t)) - (∫ t : ℝ, Φ (ℓ t)) = -lineInt Φ ℓ := by
  have hmass : (∫ t in (-1:ℝ)..1, Φ (ℓ t)) = ∫ t : ℝ, Φ (ℓ t) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have h₁ : Continuous (fun t : ℝ => ((|t| : ℝ) : ℂ)*Φ (ℓ t)) :=
    (Complex.continuous_ofReal.comp continuous_abs).mul hF
  have ht : lineInt Φ ℓ =
      (∫ t in (-1:ℝ)..1, Φ (ℓ t)) - (∫ t in (-1:ℝ)..1, ((|t| : ℝ) : ℂ)*Φ (ℓ t)) := by
    have hF' : Continuous (fun t => Φ (ℓ t)) := hF
    unfold lineInt
    rw [← intervalIntegral.integral_sub (hF'.intervalIntegrable _ _) (h₁.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro u _
    push_cast
    ring
  rw [← hmass, ht]
  ring

theorem inclusion_exclusion_main_eq_nu3F {Φ : ℝ × ℝ → ℂ}
    (hΦ : Continuous Φ) (hcΦ : HasCompactSupport Φ)
    {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    tripleFrequencyMain Φ - pairFrequencyMain (marginalD Φ) -
      pairFrequencyMain (marginalY Φ) - pairFrequencyMain (marginalX Φ) +
      2*nu3Mass Φ = nu3F Φ := by
  let d : ℝ → ℝ × ℝ := fun t => (t,-t)
  let x : ℝ → ℝ × ℝ := fun t => (t,0)
  let y : ℝ → ℝ × ℝ := fun t => (0,t)
  have cd : Continuous (Φ ∘ d) := hΦ.comp (by unfold d; fun_prop)
  have cx : Continuous (Φ ∘ x) := hΦ.comp (by unfold x; fun_prop)
  have cy : Continuous (Φ ∘ y) := hΦ.comp (by unfold y; fun_prop)
  have hz (ℓ : ℝ → ℝ × ℝ) (hℓ : ∀ t, |(ℓ t).1|+|(ℓ t).2|+|(ℓ t).1+(ℓ t).2| = 2*|t|) :
      ∀ t ∉ Set.Ioc (-1:ℝ) 1, Φ (ℓ t) = 0 := by
    intro t ht
    by_contra hn
    have H := hhex _ hn
    rw [hℓ] at H
    apply ht
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have zd := hz d (by intro t; simp [d]; ring)
  have zx := hz x (by intro t; simp [x]; ring)
  have zy := hz y (by intro t; simp [y]; ring)
  have P (Ψ : ℝ × ℝ → ℂ) (h : Continuous (Ψ ∘ d)) :
      pairLines Ψ = ∫ t in (-1:ℝ)..1, ((|t| : ℝ) : ℂ)*Ψ (d t) := by
    simpa [pairLines, pairLine, pairProfile, d] using (splitAbs h).symm
  have hswap (t : ℝ) : swap12 (d t) = x t := by simp [swap12, d, x]
  have hswap' (t : ℝ) : swap01 (swap12 (d t)) = y t := by simp [hswap, swap01, x, y]
  have D := P Φ cd
  have X0 : ((Φ ∘ swap12) ∘ d) = Φ ∘ x := by
    funext t
    simp [Function.comp_apply, hswap]
  have Y0 : (((Φ ∘ swap01) ∘ swap12) ∘ d) = Φ ∘ y := by
    funext t
    simp [Function.comp_apply, hswap']
  have X := P (Φ ∘ swap12) (X0 ▸ cx)
  have Y := P ((Φ ∘ swap01) ∘ swap12) (Y0 ▸ cy)
  simp only [Function.comp_apply, hswap] at X
  simp only [Function.comp_apply, hswap'] at Y
  have mD : marginalD Φ 0 = ∫ t : ℝ, Φ (d t) := by simp [marginalD,d]
  have mX : marginalX Φ 0 = ∫ t : ℝ, Φ (y t) := rfl
  have mY : marginalY Φ 0 = ∫ t : ℝ, Φ (x t) := rfl
  let A (p : ℝ × ℝ) : ℂ := Φ p*((|p.1| : ℝ) : ℂ)
  let B (p : ℝ × ℝ) : ℂ := Φ p*((|p.2| : ℝ) : ℂ)
  let C (p : ℝ × ℝ) : ℂ := Φ p*((|p.1+p.2| : ℝ) : ℂ)
  have ψ : Continuous (fun t : ℝ => ((|t| : ℝ) : ℂ)) := Complex.continuous_ofReal.comp continuous_abs
  have iA : Integrable A := (hΦ.mul (ψ.comp continuous_fst)).integrable_of_hasCompactSupport hcΦ.mul_right
  have iB : Integrable B := (hΦ.mul (ψ.comp continuous_snd)).integrable_of_hasCompactSupport hcΦ.mul_right
  have iC : Integrable C := (hΦ.mul (ψ.comp (continuous_fst.add continuous_snd))).integrable_of_hasCompactSupport hcΦ.mul_right
  have iΦ := hΦ.integrable_of_hasCompactSupport (μ := (volume : Measure (ℝ × ℝ))) hcΦ
  have area : 2*nu3Mass Φ - ((∫ p, A p)+(∫ p, B p)+(∫ p, C p)) =
      2*∫ p : ℝ × ℝ, (nu3Kernel p:ℂ)*Φ p := by
    unfold nu3Mass
    have iAB : Integrable (fun p => A p+B p) := iA.add iB
    have iABC : Integrable (fun p => A p+B p+C p) := iAB.add iC
    have hsum : (∫ p, A p+B p+C p) = ((∫ p, A p)+(∫ p, B p)+(∫ p, C p)) := by
      rw [integral_add iAB iC, integral_add iA iB]
    rw [← integral_const_mul, ← hsum, ← integral_sub (iΦ.const_mul 2) iABC,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : Φ p = 0
    · simp [A,B,C,hp]
    · have H := hhex _ hp
      have hp' : 0 ≤ 1-(|p.1|+|p.2|+|p.1+p.2|)/2 := by linarith
      simp only [A,B,C,nu3Kernel,max_eq_right hp']
      push_cast
      ring
  have AX := integral_marginalX hΦ hcΦ ψ
  have BY := integral_marginalY hΦ hcΦ ψ
  have CD := integral_marginalD hΦ hcΦ ψ
  change (∫ t, marginalX Φ t*((|t| : ℝ) : ℂ)) = ∫ p, A p at AX
  change (∫ t, marginalY Φ t*((|t| : ℝ) : ℂ)) = ∫ p, B p at BY
  change (∫ t, marginalD Φ t*((|t| : ℝ) : ℂ)) = ∫ p, C p at CD
  unfold tripleFrequencyMain pairFrequencyMain nu3F
  rw [D,X,Y,AX,BY,CD,mD,mX,mY,← area]
  have H1 := lineDiff d cd zd
  have H2 := lineDiff x cx zx
  have H3 := lineDiff y cy zy
  linear_combination H1 + H2 + H3
end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.inclusion_exclusion_main_eq_nu3F
