/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.ExplicitProduct
import RHTriple.PrimeArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The three-prime branch has no gamma factor. Two localized variables
already give the `T / L²` envelope needed for the same-prime diagonal. -/

noncomputable section
open Complex MeasureTheory Filter
open scoped Asymptotics

namespace XiPrime8845.RHTriple

def primeTripleKernel (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (T L a b c : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, Φ p * (dilate k T (a - frequencyShift L 0 p) *
    dilate k T (b - frequencyShift L 1 p) * dilate k T (c - frequencyShift L 2 p))

private theorem exists_bound_norm_of_compactSupport {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨M, hM⟩ := hfc.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (hM x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact le_max_right _ _

private theorem integrable_affine {f : ℝ → ℝ} (hf : Integrable f) {a b : ℝ}
    (hb : b ≠ 0) : Integrable (fun x => f (a-b*x)) := by
  have H := (hf.comp_add_right a).comp_mul_left' (neg_ne_zero.mpr hb)
  convert H using 1
  funext x
  congr 1
  ring

private theorem integral_affine (f : ℝ → ℝ) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ x, f (a-b*x)) = b⁻¹*(∫ x, f x) := by
  have he (x : ℝ) : a-b*x = (-b)*x+a := by ring
  simp_rw [he]
  rw [Measure.integral_comp_mul_left (fun y => f (y+a)) (-b), inv_neg, abs_neg,
    abs_of_pos (inv_pos.mpr hb), smul_eq_mul, integral_add_right_eq_self f a]

/-- A uniform `O(T/L²)` estimate for the actual all-prime kernel. No sign,
diagonal, or integer size restriction is needed for this bound. -/
theorem primeTripleKernel_bound {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T L : ℝ, 0 < T → 0 < L → ∀ a b c,
      ‖primeTripleKernel k Φ T L a b c‖ ≤ C * T / L^2 := by
  obtain ⟨A, hA, hks⟩ := exists_bound_norm_of_compactSupport hk hkc
  obtain ⟨B, hB, hΦs⟩ := exists_bound_norm_of_compactSupport hΦ hΦc
  let N := ∫ x, ‖k x‖
  have hN : 0 ≤ N := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨B*A*N^2, by positivity, fun T L hT hL a b c => ?_⟩
  let f : ℝ → ℝ := fun x => ‖k (T*(a-L*x))‖
  let g : ℝ → ℝ := fun y => ‖k (T*(b-L*y))‖
  have hki : Integrable (fun x => ‖k x‖) := (hk.integrable_of_hasCompactSupport hkc).norm
  have hf : Integrable f := by
    have H := integrable_affine hki (mul_ne_zero hT.ne' hL.ne') (a := T*a)
    simpa only [f, mul_sub, mul_assoc] using H
  have hg : Integrable g := by
    have H := integrable_affine hki (mul_ne_zero hT.ne' hL.ne') (a := T*b)
    simpa only [g, mul_sub, mul_assoc] using H
  let F : ℝ × ℝ → ℂ := fun p => Φ p * (dilate k T (a-frequencyShift L 0 p) *
    dilate k T (b-frequencyShift L 1 p) * dilate k T (c-frequencyShift L 2 p))
  have hDil : Continuous (dilate k T) := by unfold dilate; fun_prop
  have hF : Continuous F := by
    unfold F
    have h0 := frequencyShift_continuous L 0
    have h1 := frequencyShift_continuous L 1
    have h2 := frequencyShift_continuous L 2
    fun_prop
  have hFi : Integrable F := hF.integrable_of_hasCompactSupport (show HasCompactSupport F from hΦc.mul_right)
  have hd (x : ℝ) : ‖dilate k T x‖ = T*‖k (T*x)‖ := by
    rw [dilate, norm_mul, norm_real, Real.norm_of_nonneg hT.le]
  have hn (p : ℝ × ℝ) : ‖F p‖ ≤ (B*A*T^3) * (f p.1 * g p.2) := by
    dsimp only [F]
    simp only [norm_mul, hd]
    change ‖Φ p‖ * (T*f p.1*(T*g p.2)*(T*‖k (T*(c-frequencyShift L 2 p))‖)) ≤ _
    calc
      _ ≤ B * (T*f p.1*(T*g p.2)*(T*A)) := by
        exact mul_le_mul (hΦs p)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hks _) hT.le) (by unfold f g; positivity))
          (by unfold f g; positivity) hB
      _ = _ := by ring
  have hDom := (hf.mul_prod hg).const_mul (B*A*T^3)
  have h1 : (∫ x, f x) = (T*L)⁻¹ * N := by
    simpa only [f, N, mul_sub, mul_assoc] using
      (integral_affine (fun x : ℝ => ‖k x‖) (T*a) (mul_pos hT hL))
  have h2 : (∫ x, g x) = (T*L)⁻¹ * N := by
    simpa only [g, N, mul_sub, mul_assoc] using
      (integral_affine (fun x : ℝ => ‖k x‖) (T*b) (mul_pos hT hL))
  change ‖∫ p, F p‖ ≤ _
  calc
    _ ≤ ∫ p, ‖F p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, (B*A*T^3) * (f p.1 * g p.2) := integral_mono hFi.norm hDom hn
    _ = _ := by
      rw [integral_const_mul]
      change B*A*T^3 * (∫ p : ℝ × ℝ, f p.1 * g p.2 ∂((volume : Measure ℝ).prod volume)) = _
      rw [integral_prod_mul f g, h1, h2]
      field_simp

/-- The actual (+,+,-) same-prime diagonal is lower order for any finite
cutoff. The sign and coordinate permutations can be taken separately. -/
theorem primeTripleDiagonal_isLittleO {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (s : ℝ → Finset (ℕ × ℕ)) :
    (fun T => ∑ x ∈ s T, _root_.RHTriple.PrimeArithmetic.vonMangoldtDiagonal x •
      primeTripleKernel k Φ T (Real.log T) (Real.log x.1) (Real.log x.2)
        (-Real.log ((x.1*x.2 : ℕ) : ℝ))) =o[atTop] (fun T => T * Real.log T) := by
  obtain ⟨C, hC, hbound⟩ := primeTripleKernel_bound hk hkc hΦ hΦc
  apply _root_.RHTriple.PrimeArithmetic.diagonal_weighted_isLittleO _ _ hC
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)] with T hL hT
  intro x _
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  exact (hbound T _ hT0 hL0 _ _ _).trans (div_le_self (by positivity) (by nlinarith))

/-- In the all-prime `+,+,−` branch the log-spacing gate gives actual
vanishing, rather than a far-off-diagonal estimate. -/
theorem primeTripleOffDiag_eventually_zero {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hkc : HasCompactSupport k) {η : ℝ} (hη : 0 < η)
    (hΦ : ∀ p : ℝ × ℝ, Φ p ≠ 0 → |p.1|+|p.2|+|p.1+p.2| ≤ 2-η) :
    ∀ᶠ T in atTop, ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a*b ≠ c →
      primeTripleKernel k Φ T (Real.log T) (Real.log a) (Real.log b) (-Real.log c) = 0 := by
  obtain ⟨R₀, hR₀⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  let R := max 0 R₀
  have hR (u : ℝ) (hu : k u ≠ 0) : |u| ≤ R := (hR₀ u hu).trans (le_max_right _ _)
  have hLift := (tendsto_rpow_atTop (show 0 < η/4 by positivity)).eventually_gt_atTop (6*R)
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop (2/η)
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_ge_atTop (3*R), hLift, hL]
    with T hT hTR hBig hLT
  intro a b c ha hb hc hne
  have ht : 0 < T := by linarith
  have hlog := Real.log_nonneg hT.le
  have hmargin : 3*R/T ≤ (η/2)*Real.log T := by
    have h1 := (div_le_iff₀ ht).2 (by simpa using hTR : 3*R ≤ 1*T)
    have h2 := (div_le_iff₀ hη).1 hLT
    linarith
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  have hla := Real.log_nonneg (show (1:ℝ) ≤ a by exact_mod_cast ha)
  have hlb := Real.log_nonneg (show (1:ℝ) ≤ b by exact_mod_cast hb)
  have hlc := Real.log_nonneg (show (1:ℝ) ≤ c by exact_mod_cast hc)
  have hmul : Real.log ((a*b : ℕ):ℝ) = Real.log a + Real.log b := by
    rw [Nat.cast_mul, Real.log_mul ha'.ne' hb'.ne']
  unfold primeTripleKernel
  rw [← integral_zero (μ := (volume : Measure (ℝ × ℝ))) (G := ℂ)]
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hz : Φ p = 0
  · simp [hz]
  by_contra hn
  have h₁ : dilate k T (Real.log a-frequencyShift (Real.log T) 0 p) ≠ 0 := by
    intro h; exact hn (by simp [h])
  have h₂ : dilate k T (Real.log b-frequencyShift (Real.log T) 1 p) ≠ 0 := by
    intro h; exact hn (by simp [h])
  have h₃ : dilate k T (-Real.log c-frequencyShift (Real.log T) 2 p) ≠ 0 := by
    intro h; exact hn (by simp [h])
  have H := localized_prime_logs ht hlog hR (hΦ p hz) h₁ h₂ h₃
  have hh := H.1
  rw [abs_of_nonneg hla, abs_of_nonneg hlb, abs_neg, abs_of_nonneg hlc, ← hmul] at hh
  have hnw : Real.log ((a*b : ℕ):ℝ) + Real.log c ≤ (2-η/2)*Real.log T := by linarith
  have hgap := _root_.RHTriple.PrimeArithmetic.height_log_gap_of_margin (Nat.mul_pos ha hb) hc hne hT hnw
  rw [show (η/2)/2 = η/4 by ring, hmul] at hgap
  have H' := (le_div_iff₀ ht).1 H.2
  rw [← sub_eq_add_neg] at H'
  nlinarith

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.primeTripleKernel_bound
#print axioms XiPrime8845.RHTriple.primeTripleDiagonal_isLittleO
#print axioms XiPrime8845.RHTriple.primeTripleOffDiag_eventually_zero
