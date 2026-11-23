/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTriple.GammaKernel

/-! A real-variable evaluation of the ζ gamma transform outside the
support of the height profile's Fourier kernel. -/

noncomputable section
open Complex MeasureTheory Filter

namespace XiPrime8845.RHTriple
open Zeta23

def gammaSpacing (n : ℕ) : ℝ := 2*n + 1/2

theorem gammaSpacing_pos (n : ℕ) : 0 < gammaSpacing n := by unfold gammaSpacing; positivity

def digammaBlock (a t : ℝ) : ℝ := 1/a - a/(a^2+t^2)

theorem digammaBlock_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) :
    0 ≤ digammaBlock a t := by
  unfold digammaBlock
  rw [sub_nonneg, div_le_div_iff₀ (by positivity) ha]
  nlinarith [sq_nonneg t]

theorem digammaBlock_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    digammaBlock a t ≤ 1/a := by unfold digammaBlock; apply sub_le_self; positivity

theorem digammaBlock_mul (a t : ℝ) : digammaBlock (2*a) (2*t) = digammaBlock a t / 2 := by
  unfold digammaBlock
  rw [show (2*a)^2+(2*t)^2 = 4*(a^2+t^2) by ring]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hasSum_digammaBlock (t : ℝ) :
    HasSum (fun n => digammaBlock (gammaSpacing n) t) (Real.pi * (mu t - mu 0)) := by
  let a : ℝ := 1/4
  let u := t/2
  have ha0 : 0 < a := by norm_num [a]
  have ha1 : a < 1 := by norm_num [a]
  let F (v : ℝ) (n : ℕ) :=
    1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a)^2 + v^2)
  have hF (v) : Summable (F v) := MuFields.summable_re_terms ha0 ha1 v
  have hnext (n : ℕ) : digammaBlock (gammaSpacing (n+1)) t = (F u n - F 0 n) / 2 := by
    have hn : 0 < (n : ℝ) + 1 + a := by positivity
    rw [show gammaSpacing (n+1) = 2*((n : ℝ) + 1 + a) by simp [gammaSpacing, a]; ring,
      show t = 2*u by unfold u; ring, digammaBlock_mul]
    have he : ((n : ℝ)+1+a)/(((n : ℝ)+1+a)^2) = 1/((n : ℝ)+1+a) := by
      field_simp
    simp only [F, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero, he, digammaBlock]
    ring
  have hs : Summable (fun n => digammaBlock (gammaSpacing (n+1)) t) := by
    simp_rw [hnext]
    exact ((hF u).sub (hF 0)).div_const _
  have hsum : Summable (fun n => digammaBlock (gammaSpacing n) t) := (summable_nat_add_iff 1).1 hs
  suffices H : (∑' n, digammaBlock (gammaSpacing n) t) = Real.pi * (mu t - mu 0) by
    rw [← H]
    exact hsum.hasSum
  rw [hsum.tsum_eq_zero_add, show gammaSpacing 0 = 2*a by norm_num [gammaSpacing, a],
    show digammaBlock (2*a) t = digammaBlock a u / 2 by rw [← digammaBlock_mul, show 2*u=t by unfold u; ring]]
  simp_rw [hnext]
  rw [tsum_div_const, (hF u).tsum_sub (hF 0), MuFields.mu_eq t, MuFields.mu_eq 0]
  change digammaBlock a u / 2 + ((∑' n, F u n) - ∑' n, F 0 n) / 2 =
    Real.pi * ((1/(2*Real.pi) * (Complex.digamma ((a:ℂ)+I*(u:ℂ))).re - Real.log Real.pi/(2*Real.pi)) -
      (1/(2*Real.pi) * (Complex.digamma ((a:ℂ)+I*((0:ℝ)/2:ℝ))).re - Real.log Real.pi/(2*Real.pi)))
  rw [show (0:ℝ)/2 = 0 by norm_num, MuFields.re_digamma_vertical ha0 ha1 u,
    MuFields.re_digamma_vertical ha0 ha1 0]
  have he : a/(a^2) = 1/a := by field_simp
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0), add_zero, he, digammaBlock]
  simp only [F, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
  field_simp [Real.pi_ne_zero]
  <;> ring

def expWeight (a : ℝ) (u : ℝ) : ℂ := (Real.exp (-a * |u|) : ℂ)

theorem expWeight_integrable {a : ℝ} (ha : 0 < a) : Integrable (expWeight a) := by
  have h := EF.integrable_exp_neg_abs_half.comp_mul_left' (show 2*a ≠ 0 by positivity)
  refine h.congr (Eventually.of_forall fun u => ?_)
  change (Real.exp (-|(2*a)*u| / 2) : ℂ) = expWeight a u
  unfold expWeight
  rw [abs_mul, abs_of_pos (show 0 < 2*a by positivity)]
  congr 2 <;> ring

theorem expWeight_FT {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (∫ u, expWeight a u * cexp (-I * (r : ℂ) * u)) = ((2*a/(a^2+r^2) : ℝ) : ℂ) := by
  let b : ℝ := 2*a
  have hb : 0 < b := by dsimp [b]; positivity
  let F : ℝ → ℂ := fun u => (Real.exp (-|u|/2) : ℂ) * cexp (-I * ((r/b : ℝ) : ℂ) * u)
  have he (u : ℝ) : expWeight a u * cexp (-I * (r : ℂ) * u) = F (b*u) := by
    unfold F expWeight
    rw [abs_mul, abs_of_pos hb, show -(b * |u|) / 2 = -a * |u| by unfold b; ring]
    congr 2
    push_cast
    field_simp [show (b : ℂ) ≠ 0 by exact_mod_cast hb.ne']
  simp_rw [he]
  rw [Measure.integral_comp_mul_left F b, abs_inv, abs_of_pos hb, Complex.real_smul]
  · unfold F
    rw [EF.integral_exp_neg_abs_half]
    have hD : (0:ℝ) < a^2+r^2 := by positivity
    have hD' : (0:ℝ) < 1/4+(r/b)^2 := by positivity
    rw [show (1 / 4 : ℂ) + ((r / b : ℝ) : ℂ)^2 = ((1/4+(r/b)^2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_mul]
    congr 1
    unfold b
    field_simp [ha.ne']
    <;> ring

def inverseProfile (k : ℝ → ℂ) (x r : ℝ) : ℂ := paperFT k r * phase (-(r*x))

theorem inverseProfile_eq (k : ℝ → ℂ) (x r : ℝ) :
    inverseProfile k x r = paperFT (shift k (-x)) r := by
  rw [paperFT_shift, inverseProfile, phase]
  push_cast
  ring_nf

theorem integral_inverseProfile {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (x : ℝ) :
    (∫ r, inverseProfile k x r) = (2 * Real.pi : ℂ) * k x := by
  have h := EF.paper_inversion hk.continuous (hk.continuous.integrable_of_hasCompactSupport hkc)
    (EF.integrable_fourier_of_contDiff_two hk hkc) x
  have harg (r : ℝ) : phase (-(r*x)) = cexp (-I * r * x) := by
    unfold phase; push_cast; ring_nf
  have hc : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  rw [one_div] at h
  have h' := congrArg (fun z : ℂ => (2*Real.pi:ℂ) * z) h
  change (2*Real.pi:ℂ) * k x = (2*Real.pi:ℂ) * ((2*Real.pi:ℂ)⁻¹ * _) at h'
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h'
  simpa only [inverseProfile, harg] using h'.symm

theorem inverseProfile_integrable {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (x : ℝ) : Integrable (inverseProfile k x) := by
  refine (EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two
    (shift_contDiff hk (-x)) (shift_hasCompactSupport hkc (-x)))).congr ?_
  exact Eventually.of_forall fun r => (inverseProfile_eq k x r).symm

theorem scaledGamma_product_integrable {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Integrable (fun r : ℝ => inverseProfile k x r * (mu (T*r) : ℂ)) := by
  have h := (gammaWeight_integrable (dilate_contDiff (shift_contDiff hk (-x)) T)
    (dilate_hasCompactSupport (shift_hasCompactSupport hkc (-x)) hT)).comp_mul_left' hT.ne'
  refine h.congr (Eventually.of_forall fun r => ?_)
  change paperFT (dilate (shift k (-x)) T) ((T*r : ℝ) : ℂ) * (mu (T*r) : ℂ) = _
  rw [paperFT_dilate _ hT, Complex.ofReal_mul, mul_comm (T:ℂ),
    mul_div_cancel_right₀ _ (show (T:ℂ) ≠ 0 by exact_mod_cast hT.ne'), ← inverseProfile_eq]

theorem integral_block {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {T a : ℝ} (hT : 0 < T) (ha : 0 < a) {x : ℝ} (hx : k x = 0) :
    (∫ r : ℝ, inverseProfile k x r * (digammaBlock a (T*r) : ℂ)) =
      -(Real.pi / T : ℂ) * ∫ u, shift k (-x) u * expWeight (a/T) u := by
  let E := expWeight (a/T)
  have hE : Integrable E := expWeight_integrable (div_pos ha hT)
  have hs := shift_contDiff hk (-x)
  have hsc := shift_hasCompactSupport hkc (-x)
  have hFs := EF.integrable_fourier_of_contDiff_two hs hsc
  have hf := inverseProfile_integrable hk hkc x
  have hB (r : ℝ) : ((a/(a^2+(T*r)^2) : ℝ) : ℂ) =
      (1/(2*T) : ℂ) * ((2*(a/T)/((a/T)^2+r^2) : ℝ) : ℂ) := by
    rw [show (1/(2*T) : ℂ) = ((1/(2*T) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul]
    congr 1
    field_simp [ha.ne', hT.ne', show 0 < a^2+(T*r)^2 by positivity,
      show 0 < (a/T)^2+r^2 by positivity]
  have hp (r : ℝ) : inverseProfile k x r * ((a/(a^2+(T*r)^2) : ℝ) : ℂ) =
      (1/(2*T) : ℂ) * (paperFT (shift k (-x)) r * ∫ u, E u * cexp (-I * (r:ℂ) * u)) := by
    rw [inverseProfile_eq, hB, expWeight_FT (div_pos ha hT)]
    ring
  have hi : Integrable (fun r : ℝ => inverseProfile k x r * ((a/(a^2+(T*r)^2) : ℝ) : ℂ)) := by
    simp_rw [hp]
    exact (EF.integrable_paperFT_mul_weightFT hFs hE).const_mul _
  simp only [digammaBlock, Complex.ofReal_sub, mul_sub]
  rw [integral_sub (hf.mul_const _) hi, EF.cintegral_mul_const,
    integral_inverseProfile hk hkc x, hx, mul_zero, zero_mul, zero_sub]
  simp_rw [hp]
  rw [EF.cintegral_const_mul]
  have h := EF.integral_k_mul_weight hs.continuous (hs.continuous.integrable_of_hasCompactSupport hsc)
    hFs hE
  rw [h]
  have hp' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp [hp', hT']

/-- Outside the support the local term vanishes. Each term of the digamma
series then contributes exactly one convolution with a decaying exponential. -/
theorem scaledGamma_eq_series {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : k x = 0) :
    HasSum (fun n => ∫ u, shift k (-x) u * expWeight (gammaSpacing n / T) u)
      (-(T : ℂ) * scaledGamma k T x) := by
  let F (n : ℕ) (r : ℝ) := inverseProfile k x r * (digammaBlock (gammaSpacing n) (T*r) : ℂ)
  let b (n : ℕ) (r : ℝ) := ‖inverseProfile k x r‖ * digammaBlock (gammaSpacing n) (T*r)
  have hf := inverseProfile_integrable hk hkc x
  have hΓ := scaledGamma_product_integrable hk hkc hT x
  have hμ (r : ℝ) := hasSum_digammaBlock (T*r)
  have hm (n : ℕ) : Continuous (fun r : ℝ => (digammaBlock (gammaSpacing n) (T*r) : ℂ)) := by
    unfold digammaBlock
    have hn := gammaSpacing_pos n
    have hh : ∀ r : ℝ, gammaSpacing n ^ 2 + (T*r)^2 ≠ 0 :=
      fun r => (show 0 < gammaSpacing n ^ 2 + (T*r)^2 from by positivity).ne'
    fun_prop (disch := first | exact hh _ | positivity)
  have hb (r : ℝ) : HasSum (fun n => b n r)
      (‖inverseProfile k x r‖ * (Real.pi * (mu (T*r) - mu 0))) := (hμ r).mul_left _
  have hd : Integrable (fun r => ∑' n, b n r) := by
    simp_rw [(hb _).tsum_eq]
    have he (r : ℝ) : ‖inverseProfile k x r‖ * (Real.pi * (mu (T*r) - mu 0)) ≤
        Real.pi * (‖inverseProfile k x r * (mu (T*r) : ℂ)‖ + |mu 0| * ‖inverseProfile k x r‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hhh : mu (T*r)-mu 0 ≤ |mu (T*r)|+|mu 0| := le_trans (le_abs_self _) (abs_sub _ _)
      calc
        _ ≤ ‖inverseProfile k x r‖ * (Real.pi * (|mu (T*r)|+|mu 0|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhh Real.pi_pos.le) (norm_nonneg _)
        _ = _ := by ring
    refine ((hΓ.norm.add (hf.norm.const_mul |mu 0|)).const_mul Real.pi).mono' ?_ ?_
    · exact hf.norm.aestronglyMeasurable.mul ((gammaFacts.smooth.continuous.comp
        (continuous_const.mul continuous_id)).sub continuous_const |>.const_mul _).aestronglyMeasurable
    · exact Eventually.of_forall fun r => by
        have hh := sub_nonneg.mpr (gammaFacts.mu_zero_le (T*r))
        rw [Real.norm_of_nonneg (show 0 ≤ ‖inverseProfile k x r‖ * (Real.pi * (mu (T*r) - mu 0)) by positivity)]
        exact he r
  have hsum : HasSum (fun n => ∫ r, F n r)
      (∫ r : ℝ, inverseProfile k x r * ((Real.pi * (mu (T*r) - mu 0) : ℝ) : ℂ)) :=
    hasSum_integral_of_dominated_convergence (F := F) b
    (fun n => hf.aestronglyMeasurable.mul (hm n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun r => by
      simp only [F, b, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (digammaBlock_nonneg (gammaSpacing_pos n) (T*r)), le_refl])
    (Eventually.of_forall fun r => (hb r).summable) hd
    (Eventually.of_forall fun r => by
      have H := (Complex.ofRealCLM.hasSum (hμ r)).mul_left (inverseProfile k x r)
      exact H)
  have hgf : (∫ r : ℝ, inverseProfile k x r * ((Real.pi * (mu (T*r) - mu 0) : ℝ) : ℂ)) =
      (Real.pi : ℂ) * scaledGamma k T x := by
    push_cast
    simp_rw [show ∀ r : ℝ, inverseProfile k x r * ((Real.pi : ℂ) * ((mu (T*r) : ℂ) - (mu 0 : ℂ))) =
      (Real.pi : ℂ) * (inverseProfile k x r * (mu (T*r) : ℂ) - inverseProfile k x r * (mu 0 : ℂ))
      from fun r => by ring]
    rw [EF.cintegral_const_mul, integral_sub hΓ (hf.mul_const _), EF.cintegral_mul_const,
      integral_inverseProfile hk hkc x, hx, mul_zero, zero_mul, sub_zero]
    unfold scaledGamma inverseProfile
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  have ht := hsum.mul_left (-(T : ℂ) / Real.pi)
  rw [hgf] at ht
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have harg : (fun n : ℕ => (-(T:ℂ)/Real.pi) * ∫ r, F n r) =
      fun n : ℕ => ∫ u, shift k (-x) u * expWeight (gammaSpacing n / T) u := by
    funext n
    rw [show (∫ r, F n r) = _ from integral_block hk hkc hT (gammaSpacing_pos n) hx]
    field_simp [hπ, hT']
  have hres : (-(T:ℂ)/Real.pi) * ((Real.pi:ℂ)*scaledGamma k T x) =
      -(T:ℂ)*scaledGamma k T x := by field_simp [hπ]
  rw [harg, hres] at ht
  exact ht

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.hasSum_digammaBlock
#print axioms XiPrime8845.RHTriple.expWeight_FT
#print axioms XiPrime8845.RHTriple.scaledGamma_eq_series
