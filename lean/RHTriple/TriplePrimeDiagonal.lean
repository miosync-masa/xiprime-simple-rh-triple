/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.TriplePrimeAssembly

/-! Apply spacing and arithmetic mass bounds to the actual finite
sum of (+,+,-) kernels. For (+,+,+) the total signed log never closes. -/

noncomputable section
open Complex MeasureTheory Filter Finset
open scoped Asymptotics

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

private theorem primeWeight_product_eq_diagonal (a b : ℕ) :
    primeWeight a * primeWeight b * primeWeight (a*b) = vonMangoldtDiagonal (a,b) := by
  unfold primeWeight vonMangoldtDiagonal
  simp only [Nat.cast_mul, div_mul_div_comm]
  rw [← Real.sqrt_mul (Nat.cast_nonneg a),
    ← pow_two, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b))]

private def tripleCutDiag (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 2 N).product (Icc 2 N)).filter fun x => x.1*x.2 ∈ Icc 2 N

theorem signedTriple_ppm_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η)
    (N : ℝ → ℕ) :
    (fun T => signedTripleIntegral k Φ (N T) T true true false) =o[atTop] (fun T => T*Real.log T) := by
  refine (primeTripleDiagonal_isLittleO hk hkc hΦ hΦc (fun T => tripleCutDiag (N T))).congr'
    ?_ Filter.EventuallyEq.rfl
  filter_upwards [primeTripleOffDiag_eventually_zero hkc hη hhex] with T hT
  symm
  rw [signedTripleIntegral_eq_sum hk hΦ hΦc]
  unfold signedTripleSum tripleCutDiag
  rw [sum_filter]
  let F (x : ℕ × ℕ) : ℂ := if x.1*x.2 ∈ Icc 2 (N T) then
    vonMangoldtDiagonal x • primeTripleKernel k Φ T (Real.log T) (Real.log x.1) (Real.log x.2)
      (-Real.log ((x.1*x.2 : ℕ):ℝ)) else 0
  change _ = ∑ x ∈ (Icc 2 (N T)).product (Icc 2 (N T)), F x
  have hprod : (∑ x ∈ (Icc 2 (N T)).product (Icc 2 (N T)), F x) =
      ∑ a ∈ Icc 2 (N T), ∑ b ∈ Icc 2 (N T), F (a,b) :=
    Finset.sum_product (Icc 2 (N T)) (Icc 2 (N T)) F
  rw [hprod]
  apply sum_congr rfl; intro a ha
  apply sum_congr rfl; intro b hb
  have ha' : 0 < a := lt_of_lt_of_le (by decide) (mem_Icc.mp ha).1
  have hb' : 0 < b := lt_of_lt_of_le (by decide) (mem_Icc.mp hb).1
  have hz (c : ℕ) (hc : c ∈ Icc 2 (N T)) (hn : c ≠ a*b) :
      (primeWeight a*primeWeight b*primeWeight c) •
        primeTripleKernel k Φ T (Real.log T) (signedLog true a) (signedLog true b) (signedLog false c) = 0 := by
    simp only [signedLog, if_true, Bool.false_eq_true, if_false]
    rw [hT a b c ha' hb' (lt_of_lt_of_le (by decide) (mem_Icc.mp hc).1) hn.symm, smul_zero]
  change (∑ c ∈ Icc 2 (N T), _) = if a*b ∈ Icc 2 (N T) then _ else 0
  by_cases he : a*b ∈ Icc 2 (N T)
  · rw [if_pos he, sum_eq_single (a*b)]
    · simp only [signedLog, if_true, Bool.false_eq_true, if_false, primeWeight_product_eq_diagonal]
    · exact hz
    · exact fun hf => (hf he).elim
  · rw [if_neg he]
    exact sum_eq_zero fun c hc => hz c hc (fun h => he (h ▸ hc))

theorem signedTriple_ppp_eventually_zero {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (_hη : 0 < η)
    (hhex : ∀ x : ℝ × ℝ, Φ x ≠ 0 → |x.1|+|x.2|+|x.1+x.2| ≤ 2-η)
    (N : ℝ → ℕ) :
    ∀ᶠ T in atTop, signedTripleIntegral k Φ (N T) T true true true = 0 := by
  obtain ⟨R, hR⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_gt_atTop (R / Real.log 2)] with T hT hTR
  have ht : 0 < T := by linarith
  have hclose : R/T < Real.log 2 := by
    apply (div_lt_iff₀ ht).2
    linarith only [(div_lt_iff₀ hlog2).1 hTR]
  rw [signedTripleIntegral_eq_sum hk hΦ hΦc, signedTripleSum]
  apply sum_eq_zero; intro a ha
  apply sum_eq_zero; intro b hb
  apply sum_eq_zero; intro c hc
  simp only [signedLog, if_true]
  suffices H : primeTripleKernel k Φ T (Real.log T) (Real.log a) (Real.log b) (Real.log c) = 0 by
    rw [H, smul_zero]
  unfold primeTripleKernel
  rw [← integral_zero (μ := (volume : Measure (ℝ × ℝ))) (G := ℂ)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : Φ x = 0
  · simp [hx]
  by_contra hn
  have ha' : dilate k T (Real.log a - frequencyShift (Real.log T) 0 x) ≠ 0 :=
    fun h => hn (by simp [h])
  have hb' : dilate k T (Real.log b - frequencyShift (Real.log T) 1 x) ≠ 0 :=
    fun h => hn (by simp [h])
  have hc' : dilate k T (Real.log c - frequencyShift (Real.log T) 2 x) ≠ 0 :=
    fun h => hn (by simp [h])
  have hA : Real.log 2 ≤ Real.log a :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (mem_Icc.mp ha).1)
  have hB : Real.log 2 ≤ Real.log b :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (mem_Icc.mp hb).1)
  have hC : Real.log 2 ≤ Real.log c :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (mem_Icc.mp hc).1)
  have H := (localized_prime_logs ht (Real.log_nonneg hT.le) hR (hhex x hx) ha' hb' hc').2
  rw [abs_of_nonneg (by linarith), mul_div_assoc] at H
  linarith

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.signedTriple_ppm_isLittleO
#print axioms XiPrime8845.RHTriple.signedTriple_ppp_eventually_zero
