/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.GammaBounds
import RHTriple.PrimeKernel

/-! The actual ζ two-prime/one-gamma, and one-prime/two-gamma kernels.
The estimates use the off-support `1/d` tail, not a rapid-decay assumption. -/

noncomputable section
open Complex MeasureTheory Filter
open scoped Asymptotics

namespace XiPrime8845.RHTriple

def twoPrimeGamma (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (T L a b : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, Φ p * (dilate k T (a - frequencyShift L 0 p) *
    dilate k T (b - frequencyShift L 1 p) * gammaFactor (dilate k T) (frequencyShift L 2 p))

def onePrimeGamma (k : ℝ → ℂ) (Φ : ℝ × ℝ → ℂ) (T L a : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, Φ p * (dilate k T (a - frequencyShift L 0 p) *
    gammaFactor (dilate k T) (frequencyShift L 1 p) * gammaFactor (dilate k T) (frequencyShift L 2 p))

private theorem boundedProfile {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖Φ p‖ ≤ B := by
  obtain ⟨M, hM⟩ := hΦc.isCompact.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun p => ?_⟩
  by_cases hp : p ∈ tsupport Φ
  · exact (hM p hp).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hp, norm_zero]
    exact le_max_right _ _

private theorem integrable_translate_mul {f : ℝ → ℝ} (hf : Integrable f) (a b : ℝ)
    (hb : b ≠ 0) : Integrable (fun x => f (b*x+a)) :=
  (hf.comp_add_right a).comp_mul_left' hb

private theorem integral_translate_mul (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x, f (b*x+a)) = |b⁻¹| * (∫ x, f x) := by
  rw [Measure.integral_comp_mul_left (fun y => f (y+a)) b, smul_eq_mul,
    integral_add_right_eq_self f a]

private theorem norm_dilate (k : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    ‖dilate k T x‖ = T*‖k (T*x)‖ := by
  rw [dilate, norm_mul, norm_real, Real.norm_of_nonneg hT]

private theorem scaledGamma_simple_tail {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {R T x : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hks : ∀ u, k u ≠ 0 → |u| ≤ R) (hx : 2*(R+1) ≤ |x|) :
    ‖scaledGamma k T x‖ ≤ (10 * ∫ u, ‖k u‖) / |x| := by
  have hd : 0 < |x|-R := by linarith
  have h := scaledGamma_tail hk hkc hT hks (by linarith : R < |x|)
  have hex : Real.exp (-(|x|-R)/(4*T)) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) (by positivity))
  have hA : 0 ≤ ∫ u, ‖k u‖ := integral_nonneg fun _ => norm_nonneg _
  apply h.trans
  apply le_trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hex hd.le) (by positivity))
  rw [mul_one_div, div_le_div_iff₀ hd (by linarith)]
  nlinarith only [mul_le_mul_of_nonneg_left (show |x| ≤ 2*(|x|-R) by linarith) hA]

/-- An off-diagonal with two localized primes pays the reciprocal of the
actual signed logarithmic gap, after the `T` in the gamma factor cancels. -/
theorem twoPrimeGamma_bound {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {R : ℝ} (hR : 0 ≤ R)
    (hks : ∀ u, k u ≠ 0 → |u| ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T L a b : ℝ, 0 < T → 0 < L → 8*(R+1) ≤ T*|a+b| →
      ‖twoPrimeGamma k Φ T L a b‖ ≤ C / (L^2 * |a+b|) := by
  obtain ⟨B, hB, hΦB⟩ := boundedProfile hΦ hΦc
  let A : ℝ := ∫ u, ‖k u‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  refine ⟨20*B*A^3, by positivity, fun T L a b hT hL hsep => ?_⟩
  let D := T*|a+b|
  have hD : 0 < D := by dsimp only [D]; linarith
  let f (u : ℝ) := ‖k (T*(a-L*u))‖
  let g (v : ℝ) := ‖k (T*(b-L*v))‖
  let F (p : ℝ × ℝ) := Φ p * (dilate k T (a-frequencyShift L 0 p) *
    dilate k T (b-frequencyShift L 1 p) * gammaFactor (dilate k T) (frequencyShift L 2 p))
  have hG := gammaFactor_continuous (gammaWeight_integrable (dilate_contDiff hk T)
    (dilate_hasCompactSupport hkc hT))
  have hd : Continuous (dilate k T) := by unfold dilate; fun_prop
  have hF : Continuous F := by
    unfold F
    have h0 := frequencyShift_continuous L 0
    have h1 := frequencyShift_continuous L 1
    have h2 := frequencyShift_continuous L 2
    fun_prop
  have hFi : Integrable F := hF.integrable_of_hasCompactSupport (show HasCompactSupport F from hΦc.mul_right)
  have hKi : Integrable (fun u => ‖k u‖) := (hk.continuous.integrable_of_hasCompactSupport hkc).norm
  have hfEq (a' u : ℝ) : T*(a'-L*u) = (-(T*L))*u+T*a' := by ring
  have hv := neg_ne_zero.mpr (mul_ne_zero hT.ne' hL.ne')
  have hf : Integrable f := by simpa only [f, hfEq] using integrable_translate_mul hKi (T*a) (-(T*L)) hv
  have hg : Integrable g := by simpa only [g, hfEq] using integrable_translate_mul hKi (T*b) (-(T*L)) hv
  have hf' : (∫ u, f u) = (T*L)⁻¹*A := by
    simpa only [f, A, hfEq, inv_neg,
      abs_neg, abs_of_pos (inv_pos.mpr (mul_pos hT hL))] using
      integral_translate_mul (fun u => ‖k u‖) (T*a) (-(T*L))
  have hg' : (∫ v, g v) = (T*L)⁻¹*A := by
    simpa only [g, A, hfEq, inv_neg,
      abs_neg, abs_of_pos (inv_pos.mpr (mul_pos hT hL))] using
      integral_translate_mul (fun v => ‖k v‖) (T*b) (-(T*L))
  let M := B*T^3*(20*A/D)
  have hpt (p : ℝ × ℝ) : ‖F p‖ ≤ M * (f p.1*g p.2) := by
    let x := T*(a-L*p.1)
    let y := T*(b-L*p.2)
    let z := T*(L*p.1+L*p.2)
    have he : D = |x+y+z| := by
      rw [show x+y+z = T*(a+b) by unfold x y z; ring, abs_mul, abs_of_pos hT]
    have hnorm : ‖F p‖ = ‖Φ p‖ * (T*‖k x‖*(T*‖k y‖)*(T*‖scaledGamma k T z‖)) := by
      dsimp [F, x, y, z]
      rw [gammaFactor_dilate k hT]
      change ‖Φ p * (dilate k T (a-L*p.1) * dilate k T (b-L*p.2) *
        ((T:ℂ) * scaledGamma k T (-(T * -(L*p.1+L*p.2)))))‖ = _
      simp only [mul_neg, neg_neg, norm_mul, norm_real, Real.norm_of_nonneg hT.le, norm_dilate _ hT.le]
    rw [hnorm]
    change _ ≤ M * (‖k x‖*‖k y‖)
    by_cases hx : k x = 0
    · simp [hx]
    by_cases hy : k y = 0
    · simp [hy]
    have hsum : D ≤ |x|+|y|+|z| := by rw [he]; linarith [abs_add_le (x+y) z, abs_add_le x y]
    have hz : D/2 ≤ |z| := by linarith [hks x hx, hks y hy, show 8*(R+1) ≤ D from hsep]
    have htail := scaledGamma_simple_tail hk hkc hT hR hks (show 2*(R+1) ≤ |z| by linarith)
    have hz' : ‖scaledGamma k T z‖ ≤ 20*A/D := by
      apply htail.trans
      rw [div_le_div_iff₀ (by linarith : 0 < |z|) hD]
      nlinarith only [mul_le_mul_of_nonneg_left hz hA]
    calc
      _ ≤ B*(T*‖k x‖*(T*‖k y‖)*(T*(20*A/D))) := by gcongr; exact hΦB p
      _ = _ := by unfold M; ring
  have hDi := (hf.mul_prod hg).const_mul M
  change ‖∫ p, F p‖ ≤ _
  calc
    _ ≤ ∫ p, ‖F p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, M * (f p.1*g p.2) := integral_mono hFi.norm hDi hpt
    _ = _ := by
      rw [integral_const_mul]
      change M * (∫ p : ℝ × ℝ, f p.1*g p.2 ∂((volume : Measure ℝ).prod volume)) = _
      rw [integral_prod_mul f g, hf', hg']
      dsimp [M, D]
      have hab : 0 < |a+b| := by by_contra! h; have := mul_nonpos_of_nonneg_of_nonpos hT.le h; linarith
      field_simp

/-- With one prime, one gamma slot must carry at least a quarter of the
scaled mismatch. Use its actual tail and integrate the other in L¹. -/
theorem onePrimeGamma_bound {k : ℝ → ℂ} {Φ : ℝ × ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) {R : ℝ} (hR : 0 ≤ R)
    (hks : ∀ u, k u ≠ 0 → |u| ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T L a : ℝ, 1 ≤ T → 0 < L → 8*(R+1) ≤ T*|a| →
      ‖onePrimeGamma k Φ T L a‖ ≤ C*(1+Real.log T)/(L^2*|a|) := by
  obtain ⟨B, hB, hΦB⟩ := boundedProfile hΦ hΦc
  obtain ⟨C, hC, hL1⟩ := scaledGamma_L1 hk hkc
  let A : ℝ := ∫ u, ‖k u‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  refine ⟨80*B*A^2*C, by positivity, fun T L a hT' hL hsep => ?_⟩
  have hT : 0 < T := by linarith
  let D := T*|a|
  have hD : 0 < D := by dsimp only [D]; linarith
  let w := T*L
  have hw : 0 < w := mul_pos hT hL
  let F (p : ℝ × ℝ) := Φ p * (dilate k T (a-frequencyShift L 0 p) *
    gammaFactor (dilate k T) (frequencyShift L 1 p) * gammaFactor (dilate k T) (frequencyShift L 2 p))
  let f (u : ℝ) := ‖k (T*(a-L*u))‖
  let g (u : ℝ) := ‖scaledGamma k T u‖
  let M := B*T^3*(40*A/D)
  have hM : 0 ≤ M := by unfold M; positivity
  have hG := gammaFactor_continuous (gammaWeight_integrable (dilate_contDiff hk T)
    (dilate_hasCompactSupport hkc hT))
  have hd : Continuous (dilate k T) := by unfold dilate; fun_prop
  have hF : Continuous F := by
    unfold F
    have h0 := frequencyShift_continuous L 0
    have h1 := frequencyShift_continuous L 1
    have h2 := frequencyShift_continuous L 2
    fun_prop
  have hFi : Integrable F := hF.integrable_of_hasCompactSupport (show HasCompactSupport F from hΦc.mul_right)
  have hKi : Integrable (fun u => ‖k u‖) := (hk.continuous.integrable_of_hasCompactSupport hkc).norm
  have hfEq (u : ℝ) : T*(a-L*u) = (-w)*u+T*a := by unfold w; ring
  have hf : Integrable f := by
    simpa only [f, hfEq] using
      integrable_translate_mul hKi (T*a) (-w) (neg_ne_zero.mpr hw.ne')
  have hf' : (∫ u, f u) = w⁻¹*A := by
    simpa only [f, A, hfEq, inv_neg,
      abs_neg, abs_of_pos (inv_pos.mpr hw)] using integral_translate_mul (fun u => ‖k u‖) (T*a) (-w)
  have hg : Integrable g := (hL1 T hT').1.norm
  have hpt (u v : ℝ) : ‖F (u,v)‖ ≤ M * f u * (g (-w*v) + g (w*v+w*u)) := by
    let x := T*(a-L*u)
    let y := -w*v
    let z := w*v+w*u
    have he : D = |x+y+z| := by
      rw [show x+y+z = T*a by unfold x y z w; ring, abs_mul, abs_of_pos hT]
    have hnorm : ‖F (u,v)‖ = ‖Φ (u,v)‖ * (T*‖k x‖*(T*g y)*(T*g z)) := by
      unfold F
      rw [gammaFactor_dilate k hT, gammaFactor_dilate k hT]
      change ‖Φ (u,v) * (dilate k T (a-L*u) * ((T:ℂ)*scaledGamma k T (-(T*(L*v)))) *
        ((T:ℂ)*scaledGamma k T (-(T * -(L*u+L*v)))))‖ = _
      have hy : -(T*(L*v)) = y := by unfold y w; ring
      have hz : -(T * -(L*u+L*v)) = z := by unfold z w; ring
      rw [hy, hz]
      simp only [norm_mul, norm_real, Real.norm_of_nonneg hT.le, norm_dilate _ hT.le, g, x]
    rw [hnorm]
    change _ ≤ M * ‖k x‖ * (g y + g z)
    by_cases hx : k x = 0
    · simp [hx]
    have hsum : D ≤ |x|+|y|+|z| := by rw [he]; linarith [abs_add_le (x+y) z, abs_add_le x y]
    have hcut : D/4 ≤ |y| ∨ D/4 ≤ |z| := by
      by_contra! hh
      linarith [hks x hx, show 8*(R+1) ≤ D from hsep]
    have hsingle (r : ℝ) (hr : D/4 ≤ |r|) : g r ≤ 40*A/D := by
      apply (scaledGamma_simple_tail hk hkc hT hR hks (show 2*(R+1) ≤ |r| by linarith)).trans
      rw [div_le_div_iff₀ (by linarith : 0 < |r|) hD]
      nlinarith only [mul_le_mul_of_nonneg_left hr hA]
    have hpair : g y*g z ≤ (40*A/D)*(g y+g z) := by
      rcases hcut with hy | hz
      · calc
          _ ≤ (40*A/D)*g z := mul_le_mul_of_nonneg_right (hsingle y hy) (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (by positivity)
      · calc
          _ ≤ g y*(40*A/D) := mul_le_mul_of_nonneg_left (hsingle z hz) (norm_nonneg _)
          _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (by positivity)
    calc
      _ = ‖Φ (u,v)‖ * (T^3*‖k x‖*(g y*g z)) := by ring
      _ ≤ B * (T^3*‖k x‖*(g y*g z)) := by
        exact mul_le_mul_of_nonneg_right (hΦB (u,v))
          (show 0 ≤ T^3*‖k x‖*(g y*g z) by unfold g; positivity)
      _ ≤ B * (T^3*‖k x‖*((40*A/D)*(g y+g z))) := by gcongr
      _ = _ := by unfold M; ring
  have hrow (u : ℝ) : (∫ v, ‖F (u,v)‖) ≤ M * (2*w⁻¹*(∫ v, g v)) * f u := by
    have hy : Integrable (fun v => g (-w*v)) := hg.comp_mul_left' (neg_ne_zero.mpr hw.ne')
    have hz := integrable_translate_mul hg (w*u) w hw.ne'
    have hDom : Integrable (fun v => (M*f u)*(g (-w*v)+g (w*v+w*u))) := (hy.add hz).const_mul _
    have hc : Continuous (fun v : ℝ => ‖F (u,v)‖) := (hF.comp (continuous_const.prodMk continuous_id)).norm
    have hFi' : Integrable (fun v => ‖F (u,v)‖) := hDom.mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun v => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt u v)
    have hy' : (∫ v, g (-w*v)) = w⁻¹ * (∫ v, g v) := by
      simpa only [add_zero, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hw)] using integral_translate_mul g 0 (-w)
    have hz' : (∫ v, g (w*v+w*u)) = w⁻¹ * (∫ v, g v) := by
      simpa only [abs_of_pos (inv_pos.mpr hw)] using integral_translate_mul g (w*u) w
    calc
      _ ≤ ∫ v, (M*f u)*(g (-w*v)+g (w*v+w*u)) := integral_mono hFi' hDom (hpt u)
      _ = _ := by rw [integral_const_mul, integral_add hy hz, hy', hz']; ring
  change ‖∫ p, F p‖ ≤ _
  calc
    _ ≤ ∫ p, ‖F p‖ := norm_integral_le_integral_norm _
    _ = ∫ u, ∫ v, ‖F (u,v)‖ := integral_prod _ hFi.norm
    _ ≤ ∫ u, (M * (2*w⁻¹*(∫ v, g v))) * f u :=
      integral_mono hFi.norm.integral_prod_left (hf.const_mul _) hrow
    _ ≤ _ := by
      rw [integral_const_mul, hf']
      have hI := (hL1 T hT').2
      have hab : 0 < |a| := by by_contra! h; have := mul_nonpos_of_nonneg_of_nonpos hT.le h; linarith
      have hm : M * (2*w⁻¹*(∫ v, g v)) * (w⁻¹*A) ≤
          M * (2*w⁻¹*(C*(1+Real.log T))) * (w⁻¹*A) := by gcongr
      apply hm.trans_eq
      dsimp [M, D, w]
      field_simp
      ring

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.twoPrimeGamma_bound
#print axioms XiPrime8845.RHTriple.onePrimeGamma_bound
