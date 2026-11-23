/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedGate

/-! Exact exchange for the all-prime integral, before making any
sign, diagonal, or support reduction. -/

noncomputable section
open Complex MeasureTheory Filter Finset

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

private theorem integral_product_finsets {ι : Type*} {s : Finset ι}
    {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (A B C : ι → (ℝ × ℝ) → ℂ)
    (hA : ∀ i, Continuous (A i)) (hB : ∀ i, Continuous (B i)) (hC : ∀ i, Continuous (C i)) :
    (∫ x, Φ x * ((∑ i ∈ s, A i x) * (∑ j ∈ s, B j x) * (∑ l ∈ s, C l x))) =
      ∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, ∫ x, Φ x * (A i x * B j x * C l x) := by
  let F (i j l : ι) (x : ℝ × ℝ) := Φ x * (A i x * B j x * C l x)
  have hi (i j l) : Integrable (F i j l) :=
    (hΦ.mul (((hA i).mul (hB j)).mul (hC l))).integrable_of_hasCompactSupport hc.mul_right
  have he (x : ℝ × ℝ) : (∑ i ∈ s, ∑ j ∈ s, ∑ l ∈ s, F i j l x) =
      Φ x * ((∑ i ∈ s, A i x) * (∑ j ∈ s, B j x) * (∑ l ∈ s, C l x)) := by
    have h1 (i j : ι) : (∑ l ∈ s, F i j l x) =
        Φ x * (A i x * B j x * (∑ l ∈ s, C l x)) := by
      simp only [F, mul_sum]
    have h2 (i : ι) : (∑ j ∈ s, Φ x * (A i x * B j x * (∑ l ∈ s, C l x))) =
        Φ x * (A i x * (∑ j ∈ s, B j x) * (∑ l ∈ s, C l x)) := by
      rw [← mul_sum, ← sum_mul, ← mul_sum]
    simp_rw [h1, h2]
    rw [← mul_sum, ← sum_mul, ← sum_mul]
  simp_rw [← he]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun l _ => hi i j l]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hi i j l]
  apply sum_congr rfl
  intro j _
  exact integral_finsetSum _ fun l _ => hi i j l

def signedTripleIntegral (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ)
    (N : ℕ) (T : ℝ) (s t u : Bool) : ℂ :=
  ∫ x, Φ x * (signedPrimeFactor k T N s (frequencyShift (Real.log T) 0 x) *
    signedPrimeFactor k T N t (frequencyShift (Real.log T) 1 x) *
    signedPrimeFactor k T N u (frequencyShift (Real.log T) 2 x))

def signedTripleSum (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ)
    (N : ℕ) (T : ℝ) (s t u : Bool) : ℂ :=
  ∑ a ∈ Icc 2 N, ∑ b ∈ Icc 2 N, ∑ c ∈ Icc 2 N,
    (primeWeight a*primeWeight b*primeWeight c) •
      primeTripleKernel k Φ T (Real.log T) (signedLog s a) (signedLog t b) (signedLog u c)

theorem signedTripleIntegrand_continuous {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hΦ : Continuous Φ) (N : ℕ) (T : ℝ) (s t u : Bool) :
    Continuous (fun x => Φ x * (signedPrimeFactor k T N s (frequencyShift (Real.log T) 0 x) *
      signedPrimeFactor k T N t (frequencyShift (Real.log T) 1 x) *
      signedPrimeFactor k T N u (frequencyShift (Real.log T) 2 x))) := by
  have h (i : Fin 3) (σ : Bool) : Continuous
      (fun x => signedPrimeFactor k T N σ (frequencyShift (Real.log T) i x)) := by
    unfold signedPrimeFactor
    have hD : Continuous (dilate k T) := by unfold dilate; fun_prop
    exact continuous_finsetSum _ (fun n _ =>
      (hD.comp (continuous_const.sub (frequencyShift_continuous _ i))).const_smul (primeWeight n))
  exact hΦ.mul (((h 0 s).mul (h 1 t)).mul (h 2 u))

theorem signedTripleIntegral_eq_sum {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (N : ℕ) (T : ℝ) (s t u : Bool) :
    signedTripleIntegral k Φ N T s t u = signedTripleSum k Φ N T s t u := by
  let A (i : Fin 3) (σ : Bool) (n : ℕ) (x : ℝ × ℝ) :=
    primeWeight n • dilate k T (signedLog σ n-frequencyShift (Real.log T) i x)
  have h (i : Fin 3) (σ : Bool) (n : ℕ) : Continuous (A i σ n) := by
    have hD : Continuous (dilate k T) := by unfold dilate; fun_prop
    exact ((hD.comp (continuous_const.sub (frequencyShift_continuous _ i))).const_smul (primeWeight n))
  unfold signedTripleIntegral signedPrimeFactor signedTripleSum
  change (∫ x, Φ x * ((∑ a ∈ Icc 2 N, A 0 s a x) * (∑ b ∈ Icc 2 N, A 1 t b x) *
    (∑ c ∈ Icc 2 N, A 2 u c x))) = _
  rw [integral_product_finsets hΦ hΦc _ _ _ (h 0 s) (h 1 t) (h 2 u)]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  apply sum_congr rfl; intro c _
  rw [primeTripleKernel, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [A, real_smul, Complex.ofReal_mul]
  ring

theorem triplePrimeEF_eq_eight_signs {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (p : ℝ) {T : ℝ} (hT : 0 < T) :
    mixedEFIntegral k Φ p T 1 1 1 =
      - ∑ s : Bool, ∑ t : Bool, ∑ u : Bool, signedTripleIntegral k Φ ⌊T^p⌋₊ T s t u := by
  let A (i : Fin 3) (s : Bool) (x : ℝ × ℝ) :=
    signedPrimeFactor k T ⌊T^p⌋₊ s (frequencyShift (Real.log T) i x)
  have h (i : Fin 3) (s : Bool) : Continuous (A i s) := by
    unfold A signedPrimeFactor
    have hD : Continuous (dilate k T) := by unfold dilate; fun_prop
    exact continuous_finsetSum _ (fun n _ =>
      (hD.comp (continuous_const.sub (frequencyShift_continuous _ i))).const_smul (primeWeight n))
  calc
    _ = -∫ x, Φ x * ((∑ s : Bool, A 0 s x) * (∑ t : Bool, A 1 t x) * (∑ u : Bool, A 2 u x)) := by
      unfold mixedEFIntegral
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      change Φ x * (primeFactor (dilate k T) (p*Real.log T) (frequencyShift (Real.log T) 0 x) *
        primeFactor (dilate k T) (p*Real.log T) (frequencyShift (Real.log T) 1 x) *
        primeFactor (dilate k T) (p*Real.log T) (frequencyShift (Real.log T) 2 x)) = _
      simp only [primeFactor_eq_signed k hT, Fintype.sum_bool, A]
      ring
    _ = _ := congrArg Neg.neg (integral_product_finsets hΦ hΦc _ _ _ (h 0) (h 1) (h 2))

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.signedTripleIntegral_eq_sum
#print axioms XiPrime8845.RHTriple.triplePrimeEF_eq_eight_signs
