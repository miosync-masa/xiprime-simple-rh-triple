/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.MixedSums

/-! Exact finite-sum exchange for the two canonical mixed slot layouts.
The two-prime branch retains its paired-prime diagonal explicitly. -/

noncomputable section
open Complex MeasureTheory Filter Finset
open scoped Asymptotics

namespace XiPrime8845.RHTriple
open _root_.RHTriple.PrimeArithmetic

private theorem sum_skip_one {M : Type*} [AddCommMonoid M] {N : ℕ} {f : ℕ → M}
    (h : f 1 = 0) : (∑ n ∈ Icc 1 N, f n) = ∑ n ∈ Icc 2 N, f n := by
  symm
  apply sum_subset
  · intro n hn; simp only [mem_Icc] at hn ⊢; omega
  · intro n hn hn'
    have he : n=1 := by simp only [mem_Icc] at hn hn'; omega
    rwa [he]

def signedPrimeFactor (k : ℝ → ℂ) (T : ℝ) (N : ℕ) (s : Bool) (b : ℝ) : ℂ :=
  ∑ n ∈ Icc 2 N, primeWeight n • dilate k T (signedLog s n-b)

theorem primeFactor_eq_signed (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (p b : ℝ) :
    primeFactor (dilate k T) (p*Real.log T) b =
      -(signedPrimeFactor k T ⌊T^p⌋₊ false b + signedPrimeFactor k T ⌊T^p⌋₊ true b) := by
  unfold primeFactor signedPrimeFactor
  rw [show Real.exp (p*Real.log T)=T^p by rw [Real.rpow_def_of_pos hT, mul_comm]]
  congr 1
  rw [show Ioc 0 ⌊T^p⌋₊ = Icc 1 ⌊T^p⌋₊ by ext n; simp; omega, sum_skip_one (by simp)]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  simp only [signedLog, Bool.false_eq_true, if_false, if_true, real_smul, primeWeight]
  ring

private def mixedFactor (k : ℝ → ℂ) (T L : ℝ) (i : Fin 3) (a : Option ℝ)
    (x : ℝ × ℝ) : ℂ :=
  match a with
  | none => gammaFactor (dilate k T) (frequencyShift L i x)
  | some b => dilate k T (b-frequencyShift L i x)

private theorem continuous_mixedFactor {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T) (L : ℝ) (i : Fin 3) (a : Option ℝ) :
    Continuous (mixedFactor k T L i a) := by
  have h := frequencyShift_continuous L i
  cases a with
  | none => exact (gammaFactor_continuous (gammaWeight_integrable (dilate_contDiff hk T)
      (dilate_hasCompactSupport hkc hT))).comp h
  | some a => exact (dilate_contDiff hk T).continuous.comp (continuous_const.sub h)

private theorem integrable_mixedProduct {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (L : ℝ) (a b c : Option ℝ) :
    Integrable (fun x : ℝ × ℝ => Φ x *
      (mixedFactor k T L 0 a x * mixedFactor k T L 1 b x * mixedFactor k T L 2 c x)) := by
  have H := hΦ.mul (((continuous_mixedFactor hk hkc hT L 0 a).mul
    (continuous_mixedFactor hk hkc hT L 1 b)).mul (continuous_mixedFactor hk hkc hT L 2 c))
  exact H.integrable_of_hasCompactSupport hΦc.mul_right

theorem onePrimeFactor_integral_eq {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (N : ℕ) (s : Bool) :
    (∫ x : ℝ × ℝ, Φ x * (signedPrimeFactor k T N s (frequencyShift (Real.log T) 0 x) *
      gammaFactor (dilate k T) (frequencyShift (Real.log T) 1 x) *
      gammaFactor (dilate k T) (frequencyShift (Real.log T) 2 x))) = onePrimeSum k Φ s N T := by
  let L := Real.log T
  let F (n : ℕ) (x : ℝ × ℝ) := Φ x * (dilate k T (signedLog s n-frequencyShift L 0 x) *
    gammaFactor (dilate k T) (frequencyShift L 1 x) * gammaFactor (dilate k T) (frequencyShift L 2 x))
  have he (x : ℝ × ℝ) : Φ x * (signedPrimeFactor k T N s (frequencyShift L 0 x) *
      gammaFactor (dilate k T) (frequencyShift L 1 x) * gammaFactor (dilate k T) (frequencyShift L 2 x)) =
      ∑ n ∈ Icc 2 N, primeWeight n • F n x := by
    simp only [signedPrimeFactor, F, real_smul, sum_mul, mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  change (∫ x : ℝ × ℝ, Φ x * (signedPrimeFactor k T N s (frequencyShift L 0 x) *
    gammaFactor (dilate k T) (frequencyShift L 1 x) * gammaFactor (dilate k T) (frequencyShift L 2 x))) = _
  simp_rw [he]
  have hi (n : ℕ) : Integrable (fun x => primeWeight n • F n x) := by
    have hFn : Integrable (F n) := integrable_mixedProduct hk hkc hT hΦ hΦc L
      (some (signedLog s n)) none none
    exact hFn.fun_smul (primeWeight n)
  rw [integral_finsetSum _ fun n _ => hi n]
  simp only [integral_smul, onePrimeSum, onePrimeGamma, F, L]

def twoSignedPrimeSum (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s t : Bool) (N : ℕ) (T : ℝ) : ℂ :=
  ∑ n ∈ Icc 2 N, ∑ m ∈ Icc 2 N, (primeWeight n*primeWeight m) •
    twoPrimeGamma k Φ T (Real.log T) (signedLog s n) (signedLog t m)

theorem twoPrimeFactor_integral_eq {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (N : ℕ) (s t : Bool) :
    (∫ x : ℝ × ℝ, Φ x * (signedPrimeFactor k T N s (frequencyShift (Real.log T) 0 x) *
      signedPrimeFactor k T N t (frequencyShift (Real.log T) 1 x) *
      gammaFactor (dilate k T) (frequencyShift (Real.log T) 2 x))) = twoSignedPrimeSum k Φ s t N T := by
  let L := Real.log T
  let F (n m : ℕ) (x : ℝ × ℝ) := Φ x * (dilate k T (signedLog s n-frequencyShift L 0 x) *
    dilate k T (signedLog t m-frequencyShift L 1 x) * gammaFactor (dilate k T) (frequencyShift L 2 x))
  have he (x : ℝ × ℝ) : Φ x * (signedPrimeFactor k T N s (frequencyShift L 0 x) *
      signedPrimeFactor k T N t (frequencyShift L 1 x) * gammaFactor (dilate k T) (frequencyShift L 2 x)) =
      ∑ n ∈ Icc 2 N, ∑ m ∈ Icc 2 N, (primeWeight n*primeWeight m) • F n m x := by
    simp only [signedPrimeFactor, F, real_smul]
    rw [sum_mul_sum]
    simp only [sum_mul, mul_sum]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by push_cast; ring
  change (∫ x : ℝ × ℝ, Φ x * (signedPrimeFactor k T N s (frequencyShift L 0 x) *
    signedPrimeFactor k T N t (frequencyShift L 1 x) * gammaFactor (dilate k T) (frequencyShift L 2 x))) = _
  simp_rw [he]
  have hi (n m : ℕ) : Integrable (fun x => (primeWeight n*primeWeight m) • F n m x) := by
    have hFnm : Integrable (F n m) := integrable_mixedProduct hk hkc hT hΦ hΦc L
      (some (signedLog s n)) (some (signedLog t m)) none
    exact hFnm.fun_smul (primeWeight n*primeWeight m)
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hi n m]
  unfold twoSignedPrimeSum
  apply sum_congr rfl
  intro n _
  rw [integral_finsetSum _ fun m _ => hi n m]
  simp only [integral_smul, twoPrimeGamma, F, L]

def pairedPrimeDiagonal (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s : Bool) (N : ℕ) (T : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, (primeWeight n * primeWeight n) •
    twoPrimeGamma k Φ T (Real.log T) (signedLog s n) (signedLog (!s) n)

theorem twoSignedPrimeSum_opp_eq (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (s : Bool) (N : ℕ) (T : ℝ) :
    twoSignedPrimeSum k Φ s (!s) N T = pairedPrimeDiagonal k Φ s N T + oppositeSignOffDiagSum k Φ s N T := by
  let f (n m : ℕ) := (primeWeight n*primeWeight m) •
    twoPrimeGamma k Φ T (Real.log T) (signedLog s n) (signedLog (!s) m)
  have h1 (n : ℕ) : f 1 n = 0 := by simp [f, primeWeight]
  have h2 (n : ℕ) : f n 1 = 0 := by simp [f, primeWeight]
  change (∑ n ∈ Icc 2 N, ∑ m ∈ Icc 2 N, f n m) = _
  rw [← sum_skip_one (show (∑ m ∈ Icc 2 N, f 1 m) = 0 by simp [h1])]
  simp_rw [← sum_skip_one (h2 _)]
  unfold pairedPrimeDiagonal oppositeSignOffDiagSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  change (∑ m ∈ Icc 1 N, f n m) = f n n + ∑ m ∈ Icc 1 N, if n=m then 0 else f n m
  rw [← sum_erase_add _ _ hn]
  have he : ∑ m ∈ Icc 1 N, (if n=m then 0 else f n m) = ∑ m ∈ (Icc 1 N).erase n, f n m := by
    rw [← sum_erase_add _ _ hn, if_pos rfl, add_zero]
    apply sum_congr rfl
    intro m hm
    rw [if_neg (mem_erase.mp hm).1.symm]
  rw [he]
  ring

def mixedEFIntegral (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (p T : ℝ) (i j l : Fin 3) : ℂ :=
  ∫ x, Φ x *
    (factors (dilate k T) (p*Real.log T) i (frequencyShift (Real.log T) 0 x) *
     factors (dilate k T) (p*Real.log T) j (frequencyShift (Real.log T) 1 x) *
     factors (dilate k T) (p*Real.log T) l (frequencyShift (Real.log T) 2 x))

private theorem signedPrimeFactor_continuous {k : ℝ → ℂ} (hk : Continuous k)
    (T : ℝ) (N : ℕ) (s : Bool) : Continuous (signedPrimeFactor k T N s) := by
  unfold signedPrimeFactor
  simp only [real_smul]
  refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
  unfold dilate
  fun_prop

private theorem integrable_signedFactors {Φ a b c : ℝ × ℝ → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Integrable (fun x => Φ x * (a x * b x * c x)) :=
  (hΦ.mul ((ha.mul hb).mul hc)).integrable_of_hasCompactSupport hΦc.mul_right

theorem mixedEF_one_eq {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (p : ℝ) {T : ℝ} (hT : 0 < T) :
    mixedEFIntegral k Φ p T 1 2 2 =
      -(onePrimeSum k Φ false ⌊T^p⌋₊ T + onePrimeSum k Φ true ⌊T^p⌋₊ T) := by
  let L := Real.log T
  let N := ⌊T^p⌋₊
  let P (s : Bool) (x : ℝ × ℝ) := signedPrimeFactor k T N s (frequencyShift L 0 x)
  let G (i : Fin 3) (x : ℝ × ℝ) := gammaFactor (dilate k T) (frequencyShift L i x)
  let F (s : Bool) (x : ℝ × ℝ) := Φ x * (P s x * G 1 x * G 2 x)
  have hF (s : Bool) : Integrable (F s) := integrable_signedFactors hΦ hΦc
    ((signedPrimeFactor_continuous hk.continuous T N s).comp (frequencyShift_continuous L 0))
    (continuous_mixedFactor hk hkc hT L 1 none) (continuous_mixedFactor hk hkc hT L 2 none)
  calc
    _ = ∫ x, -(F false x + F true x) := by
      unfold mixedEFIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      change Φ x * (primeFactor (dilate k T) (p*L) (frequencyShift L 0 x) * G 1 x * G 2 x) = _
      rw [primeFactor_eq_signed k hT]
      change Φ x * (-(P false x + P true x) * G 1 x * G 2 x) = _
      unfold F
      ring
    _ = _ := by
      rw [integral_neg, integral_add (hF false) (hF true)]
      simp only [F, P, G, N, L, onePrimeFactor_integral_eq hk hkc hT hΦ hΦc]

theorem mixedEF_two_eq {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) (p : ℝ) {T : ℝ} (hT : 0 < T) :
    mixedEFIntegral k Φ p T 1 1 2 =
      (twoSignedPrimeSum k Φ false false ⌊T^p⌋₊ T + twoSignedPrimeSum k Φ false true ⌊T^p⌋₊ T) +
      (twoSignedPrimeSum k Φ true false ⌊T^p⌋₊ T + twoSignedPrimeSum k Φ true true ⌊T^p⌋₊ T) := by
  let L := Real.log T
  let N := ⌊T^p⌋₊
  let P (i : Fin 3) (s : Bool) (x : ℝ × ℝ) := signedPrimeFactor k T N s (frequencyShift L i x)
  let G (x : ℝ × ℝ) := gammaFactor (dilate k T) (frequencyShift L 2 x)
  let F (s t : Bool) (x : ℝ × ℝ) := Φ x * (P 0 s x * P 1 t x * G x)
  have hF (s t : Bool) : Integrable (F s t) := integrable_signedFactors hΦ hΦc
    ((signedPrimeFactor_continuous hk.continuous T N s).comp (frequencyShift_continuous L 0))
    ((signedPrimeFactor_continuous hk.continuous T N t).comp (frequencyShift_continuous L 1))
    (continuous_mixedFactor hk hkc hT L 2 none)
  calc
    _ = ∫ x, (F false false x + F false true x) + (F true false x + F true true x) := by
      unfold mixedEFIntegral
      apply integral_congr_ae
      filter_upwards [] with x
      change Φ x * (primeFactor (dilate k T) (p*L) (frequencyShift L 0 x) *
        primeFactor (dilate k T) (p*L) (frequencyShift L 1 x) * G x) = _
      rw [primeFactor_eq_signed k hT, primeFactor_eq_signed k hT]
      change Φ x * (-(P 0 false x + P 0 true x) * -(P 1 false x + P 1 true x) * G x) = _
      unfold F
      ring
    _ = _ := by
      have hsplit : (∫ x, (F false false x + F false true x) + (F true false x + F true true x)) =
          (∫ x, F false false x + F false true x) + ∫ x, F true false x + F true true x :=
        integral_add ((hF false false).add (hF false true)) ((hF true false).add (hF true true))
      rw [hsplit, integral_add (hF false false) (hF false true), integral_add (hF true false) (hF true true)]
      simp only [F, P, G, N, L, twoPrimeFactor_integral_eq hk hkc hT hΦ hΦc]

theorem mixedEF_canonical_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    let p := 1-η/4
    ((fun T => mixedEFIntegral k Φ p T 1 2 2) =o[atTop] (fun T => T*Real.log T)) ∧
    ((fun T => mixedEFIntegral k Φ p T 1 1 2 -
      (pairedPrimeDiagonal k Φ false ⌊T^p⌋₊ T + pairedPrimeDiagonal k Φ true ⌊T^p⌋₊ T))
      =o[atTop] (fun T => T*Real.log T)) := by
  let p := 1-η/4
  have hF (s : Bool) := mixedSums_hex_isLittleO hk hkc hΦ hΦc hη hη1 s false
  have hO (s : Bool) := oppositeSignOffDiagSum_isLittleO hk hkc hΦ hΦc hη hη1 s
  constructor
  · refine ((hF false).1.add (hF true).1).neg_left.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (mixedEF_one_eq hk hkc hΦ hΦc p hT).symm
  · refine (((hF false).2.1.add (hO false)).add ((hO true).add (hF true).2.1)).congr'
      ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    change ((sameSignPrimeSum k Φ false ⌊T^p⌋₊ T + oppositeSignOffDiagSum k Φ false ⌊T^p⌋₊ T) +
      (oppositeSignOffDiagSum k Φ true ⌊T^p⌋₊ T + sameSignPrimeSum k Φ true ⌊T^p⌋₊ T)) = _
    let N := ⌊T^p⌋₊
    have h₁ : twoSignedPrimeSum k Φ false true N T =
        pairedPrimeDiagonal k Φ false N T + oppositeSignOffDiagSum k Φ false N T :=
      twoSignedPrimeSum_opp_eq k Φ false N T
    have h₂ : twoSignedPrimeSum k Φ true false N T =
        pairedPrimeDiagonal k Φ true N T + oppositeSignOffDiagSum k Φ true N T :=
      twoSignedPrimeSum_opp_eq k Φ true N T
    rw [mixedEF_two_eq hk hkc hΦ hΦc p hT, h₁, h₂]
    change (sameSignPrimeSum k Φ false N T + oppositeSignOffDiagSum k Φ false N T) +
        (oppositeSignOffDiagSum k Φ true N T + sameSignPrimeSum k Φ true N T) =
      ((sameSignPrimeSum k Φ false N T +
        (pairedPrimeDiagonal k Φ false N T + oppositeSignOffDiagSum k Φ false N T)) +
        ((pairedPrimeDiagonal k Φ true N T + oppositeSignOffDiagSum k Φ true N T) +
          sameSignPrimeSum k Φ true N T)) -
        (pairedPrimeDiagonal k Φ false N T + pairedPrimeDiagonal k Φ true N T)
    abel

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.primeFactor_eq_signed
#print axioms XiPrime8845.RHTriple.onePrimeFactor_integral_eq
#print axioms XiPrime8845.RHTriple.twoPrimeFactor_integral_eq
#print axioms XiPrime8845.RHTriple.twoSignedPrimeSum_opp_eq
#print axioms XiPrime8845.RHTriple.mixedEF_canonical_isLittleO
