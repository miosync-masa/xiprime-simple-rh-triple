/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedAssembly
import RHTriple.MixedSlots

/-! The two canonical estimates supply all six mixed prime/gamma terms of the
actual explicit formula. The three opposite-sign equal-index pairs are retained. -/

noncomputable section
open Complex MeasureTheory Filter
open scoped Asymptotics

namespace XiPrime8845.RHTriple

theorem mixedEF_swap01 (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ)
    (p T : ℝ) (i j l : Fin 3) :
    mixedEFIntegral k Φ p T i j l = mixedEFIntegral k (Φ ∘ swap01) p T j i l := by
  unfold mixedEFIntegral
  rw [← integral_swap01]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Function.comp_apply, (slots_swap01 (Real.log T) x).1,
    (slots_swap01 (Real.log T) x).2.1, (slots_swap01 (Real.log T) x).2.2]
  ring

theorem mixedEF_swap12 {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (p : ℝ) {T : ℝ} (hT : 0 < T) (i j l : Fin 3) :
    mixedEFIntegral k Φ p T i j l = mixedEFIntegral k (Φ ∘ swap12) p T i l j := by
  let L := Real.log T
  let B := p*L
  let F (x : ℝ × ℝ) := Φ x * (factors (dilate k T) B i (frequencyShift L 0 x) *
    factors (dilate k T) B j (frequencyShift L 1 x) * factors (dilate k T) B l (frequencyShift L 2 x))
  have h (a q : Fin 3) : Continuous fun x : ℝ × ℝ => factors (dilate k T) B a (frequencyShift L q x) :=
    (factors_continuous (dilate_contDiff hk T) (dilate_hasCompactSupport hkc hT) B a).comp
      (frequencyShift_continuous L q)
  calc
    _ = ∫ x, F (swap12 x) := (integral_swap12 (hΦ.mul (((h i 0).mul (h j 1)).mul (h l 2)))
      (hΦc.mul_right : HasCompactSupport F)).symm
    _ = _ := by
      unfold mixedEFIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [F, L, B, Function.comp_apply, (slots_swap12 (Real.log T) x).1,
        (slots_swap12 (Real.log T) x).2.1, (slots_swap12 (Real.log T) x).2.2]
      ring

def pairedMain (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (p T : ℝ) : ℂ :=
  pairedPrimeDiagonal k Φ false ⌊T^p⌋₊ T + pairedPrimeDiagonal k Φ true ⌊T^p⌋₊ T

def mixedRemainder (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (p T : ℝ) : ℂ :=
  (mixedEFIntegral k Φ p T 1 2 2 + mixedEFIntegral k Φ p T 2 1 2 +
    mixedEFIntegral k Φ p T 2 2 1) +
  ((mixedEFIntegral k Φ p T 1 1 2 - pairedMain k Φ p T) +
    (mixedEFIntegral k Φ p T 1 2 1 - pairedMain k (Φ ∘ swap12) p T) +
    (mixedEFIntegral k Φ p T 2 1 1 - pairedMain k ((Φ ∘ swap01) ∘ swap12) p T))

theorem mixedRemainder_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (fun T => mixedRemainder k Φ (1-η/4) T) =o[atTop] (fun T => T*Real.log T) := by
  let p := 1-η/4
  have H {Ψ : ℝ × ℝ → ℂ} (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :=
    mixedEF_canonical_isLittleO hk hkc hΨ hΨc hη hη1
  have h01 := hΦ.comp swap01.continuous
  have h01c := hΦc.comp_homeomorph swap01
  have h12 := hΦ.comp swap12.continuous
  have h12c := hΦc.comp_homeomorph swap12
  have hone := ((H hΦ hΦc).1.add (H h01 h01c).1).add
    (H (h12.comp swap01.continuous) (h12c.comp_homeomorph swap01)).1
  have htwo := ((H hΦ hΦc).2.add (H h12 h12c).2).add
    (H (h01.comp swap12.continuous) (h01c.comp_homeomorph swap12)).2
  refine (hone.add htwo).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have h₁ := mixedEF_swap01 k Φ p T 2 1 2
  have h₂ := (mixedEF_swap12 hk hkc hΦ hΦc p hT 2 2 1).trans
    (mixedEF_swap01 k (Φ ∘ swap12) p T 2 1 2)
  have h₃ := mixedEF_swap12 hk hkc hΦ hΦc p hT 1 2 1
  have h₄ := (mixedEF_swap01 k Φ p T 2 1 1).trans
    (mixedEF_swap12 hk hkc h01 h01c p hT 1 2 1)
  change _ = mixedRemainder k Φ p T
  rw [mixedRemainder, h₁, h₂, h₃, h₄]
  rfl

theorem strict_hexagon_EF_cutoff {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hkc : HasCompactSupport k) {η : ℝ} (hη : 0 < η)
    (hΦ : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    ∃ R : ℝ, (∀ x, k x ≠ 0 → |x| ≤ R) ∧
      ∀ᶠ T in atTop, 0 < T ∧
        ∀ x, Φ x ≠ 0 → ∀ i, R/T + |frequencyShift (Real.log T) i x| ≤ (1-η/4)*Real.log T := by
  obtain ⟨R, hR⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  refine ⟨R, hR, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop R,
    Real.tendsto_log_atTop.eventually_ge_atTop (4/η)] with T hT hTR hTL
  have ht : 0 < T := by linarith
  refine ⟨ht, fun x hx i => ?_⟩
  have hb := frequencyShift_hex_bound (Real.log_nonneg hT.le) (hΦ x hx) i
  have hd : R/T ≤ 1 := (div_le_one ht).2 hTR
  have hh := (div_le_iff₀ hη).1 hTL
  nlinarith only [hb, hd, hh]

def smoothedTriple (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  ∑' r : (ZetaZero × ZetaZero) × ZetaZero, ∫ x : ℝ × ℝ, Φ x *
    (tripleWeight (fun ρ : ZetaZero => (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
      Zeta23.paperFT k (Zeta23.gammaOf ρ / (T : ℂ))) r *
      phase (differences (Real.log T) (r.1.1 : ℂ).im (r.1.2 : ℂ).im (r.2 : ℂ).im x))

def polarRemainder (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (p T : ℝ) : ℂ :=
  ∑ js : (Fin 3 × Fin 3) × Fin 3, if js.1.1 = 0 ∨ js.1.2 = 0 ∨ js.2 = 0 then
    mixedEFIntegral k Φ p T js.1.1 js.1.2 js.2 else 0

def retainedPrimePairs (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (p T : ℝ) : ℂ :=
  pairedMain k Φ p T + pairedMain k (Φ ∘ swap12) p T +
    pairedMain k ((Φ ∘ swap01) ∘ swap12) p T

theorem smoothedTriple_eventually_mixed_split (hRH : RiemannHypothesis)
    {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η) :
    let p := 1-η/4
    ∀ᶠ T in atTop, smoothedTriple k Φ T =
      polarRemainder k Φ p T + mixedEFIntegral k Φ p T 2 2 2 +
        mixedEFIntegral k Φ p T 1 1 1 + retainedPrimePairs k Φ p T +
        mixedRemainder k Φ p T := by
  let p := 1-η/4
  obtain ⟨R, hR, hcut⟩ := strict_hexagon_EF_cutoff hkc hη hhex
  filter_upwards [hcut] with T ⟨hT, hTcut⟩
  have hb (x : ℝ) (hx : dilate k T x ≠ 0) : |x| ≤ R/T := by
    have h := hR (T*x) (fun h => hx (by simp [dilate, h]))
    rwa [abs_mul, abs_of_pos hT, mul_comm T, ← le_div_iff₀ hT] at h
  have H := scaled_zeta_triple_explicit_split hRH hk hkc hT hb hΦ hΦc hTcut
  change smoothedTriple k Φ T =
    ∑ js : (Fin 3 × Fin 3) × Fin 3, mixedEFIntegral k Φ p T js.1.1 js.1.2 js.2 at H
  change smoothedTriple k Φ T = _
  rw [H]
  simp [polarRemainder, retainedPrimePairs, mixedRemainder, Fintype.sum_prod_type, Fin.sum_univ_three]
  abel

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.mixedEF_swap01
#print axioms XiPrime8845.RHTriple.mixedEF_swap12
#print axioms XiPrime8845.RHTriple.mixedRemainder_isLittleO
#print axioms XiPrime8845.RHTriple.strict_hexagon_EF_cutoff
#print axioms XiPrime8845.RHTriple.smoothedTriple_eventually_mixed_split
