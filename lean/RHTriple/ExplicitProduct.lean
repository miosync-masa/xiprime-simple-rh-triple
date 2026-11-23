/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Zeta23.WeilEF.Main
import Zeta23.Statement
import Zeta23.ExplicitFormula.Bridge
import Zeta23.GammaFacts.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Exact threefold ζ explicit formula with a smooth height transform.
The equality is before taking a large-height limit and before removing
repeated slots. The Fourier convention is that of `Zeta23.paperFT`. -/

noncomputable section
open Complex MeasureTheory

namespace XiPrime8845.RHTriple
open Zeta23

def shift (k : ℝ → ℂ) (b : ℝ) : ℝ → ℂ := fun x => k (x - b)

theorem shift_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (b : ℝ) :
    ContDiff ℝ 2 (shift k b) :=
  hk.comp (contDiff_id.sub contDiff_const)

theorem shift_hasCompactSupport {k : ℝ → ℂ} (hk : HasCompactSupport k) (b : ℝ) :
    HasCompactSupport (shift k b) := by
  change HasCompactSupport (fun x : ℝ => k (x - b))
  simp_rw [sub_eq_add_neg]
  exact hk.comp_homeomorph (Homeomorph.addRight (-b))

theorem paperFT_shift (k : ℝ → ℂ) (b : ℝ) (z : ℂ) :
    paperFT (shift k b) z = paperFT k z * Complex.exp (I * z * b) := by
  unfold paperFT
  rw [← EF.cintegral_mul_const]
  rw [← integral_add_right_eq_self (fun u : ℝ => shift k b u * Complex.exp (I * z * u)) b]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [shift, add_sub_cancel_right, Complex.ofReal_add]
  rw [mul_add, Complex.exp_add]
  simp only [mul_assoc]

/-- On the Fourier side, the height weight `h(γ/T)` uses `T k(T x)`. -/
def dilate (k : ℝ → ℂ) (T : ℝ) : ℝ → ℂ := fun x => (T : ℂ) * k (T * x)

theorem dilate_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (T : ℝ) :
    ContDiff ℝ 2 (dilate k T) :=
  contDiff_const.mul (hk.comp (contDiff_const.mul contDiff_id))

theorem dilate_hasCompactSupport {k : ℝ → ℂ} (hk : HasCompactSupport k) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (dilate k T) := by
  exact (hk.comp_homeomorph (Homeomorph.mulLeft₀ T hT.ne')).mul_left

theorem paperFT_dilate (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (z : ℂ) :
    paperFT (dilate k T) z = paperFT k (z / (T : ℂ)) := by
  let F : ℝ → ℂ := fun y => k y * Complex.exp (I * (z / (T : ℂ)) * y)
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have harg (x : ℝ) : I * (z / (T : ℂ)) * ((T * x : ℝ) : ℂ) = I * z * x := by
    push_cast
    field_simp
  calc
    paperFT (dilate k T) z = (T : ℂ) * ∫ x : ℝ, F (T * x) := by
      rw [← EF.cintegral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      change ((T : ℂ) * k (T * x)) * Complex.exp (I * z * (x : ℂ)) =
        (T : ℂ) * (k (T * x) * Complex.exp (I * (z / (T : ℂ)) * ((T * x : ℝ) : ℂ)))
      rw [harg x, mul_assoc]
    _ = paperFT k (z / (T : ℂ)) := by
      rw [Measure.integral_comp_mul_left, abs_inv, abs_of_pos hT, Complex.real_smul, Complex.ofReal_inv,
        ← mul_assoc, mul_inv_cancel₀ hT', one_mul]
      rfl

def phase (x : ℝ) : ℂ := Complex.exp (I * (x : ℂ))

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_I_mul_ofReal x

theorem continuous_phase : Continuous phase := by unfold phase; fun_prop

def differences (L x y z : ℝ) (p : ℝ × ℝ) : ℝ :=
  (x - z) * (L * p.1) + (y - z) * (L * p.2)

theorem phase_product (L x y z : ℝ) (p : ℝ × ℝ) :
    phase (x * (L * p.1)) * phase (y * (L * p.2)) * phase (z * (-(L * p.1 + L * p.2))) =
      phase (differences L x y z p) := by
  simp only [phase, ← Complex.exp_add, differences]
  congr 1
  push_cast
  ring

section Exchange

variable {ι : Type*}

def pairPhaseSum (a : ι → ℂ) (γ : ι → ℝ) (b : ℝ) : ℂ :=
  ∑' i, a i * phase (γ i * b)

def tripleWeight (a : ι → ℂ) (r : (ι × ι) × ι) : ℂ := a r.1.1 * a r.1.2 * a r.2

theorem integrable_tripleWeight (Φ : ℝ × ℝ → ℂ) (hΦ : Integrable Φ) (a : ι → ℂ)
    (γ : ι → ℝ) (L : ℝ) (r : (ι × ι) × ι) :
    Integrable (fun p => Φ p * (tripleWeight a r *
      phase (differences L (γ r.1.1) (γ r.1.2) (γ r.2) p))) := by
  apply hΦ.mul_bdd (c := ‖tripleWeight a r‖)
  · apply Continuous.aestronglyMeasurable
    apply continuous_const.mul (continuous_phase.comp ?_)
    unfold differences
    fun_prop
  · exact Filter.Eventually.of_forall fun p => by rw [norm_mul, norm_phase, mul_one]

/-- Uniform absolute convergence in the two frequencies, followed by dominated
exchange with the frequency-plane integral. The height tuple is ordered. -/
theorem integral_product [Countable ι] (Φ : ℝ × ℝ → ℂ) (hΦ : Integrable Φ) (a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖)) (γ : ι → ℝ) (L : ℝ) :
    (∫ p : ℝ × ℝ, Φ p * (pairPhaseSum a γ (L * p.1) * pairPhaseSum a γ (L * p.2) *
      pairPhaseSum a γ (-(L * p.1 + L * p.2)))) =
    ∑' r : (ι × ι) × ι, ∫ p : ℝ × ℝ, Φ p * (tripleWeight a r *
      phase (differences L (γ r.1.1) (γ r.1.2) (γ r.2) p)) := by
  have hn (b : ℝ) : Summable (fun i => ‖a i * phase (γ i * b)‖) := by
    simpa only [norm_mul, norm_phase, mul_one] using ha
  have hW : Summable (fun r : (ι × ι) × ι => ‖tripleWeight a r‖) :=
    (ha.mul_norm ha).mul_norm ha
  let F := fun (r : (ι × ι) × ι) (p : ℝ × ℝ) => Φ p * (tripleWeight a r *
      phase (differences L (γ r.1.1) (γ r.1.2) (γ r.2) p))
  have hF : ∀ r, Integrable (F r) := integrable_tripleWeight Φ hΦ a γ L
  have hsum : Summable (fun r => ∫ p, ‖F r p‖) := by
    have h : (fun r => ∫ p, ‖F r p‖) =
        fun r => (∫ p, ‖Φ p‖) * ‖tripleWeight a r‖ := by
      funext r
      simp only [F, norm_mul, norm_phase, mul_one]
      exact integral_mul_const _ _
    rw [h]
    exact hW.mul_left _
  rw [show (∑' r, ∫ p, F r p) = ∫ p, ∑' r, F r p from
    integral_tsum_of_summable_integral_norm hF hsum]
  apply integral_congr_ae
  filter_upwards [] with p
  unfold pairPhaseSum
  rw [tsum_mul_tsum_of_summable_norm (hn _) (hn _)]
  rw [tsum_mul_tsum_of_summable_norm ((hn _).mul_norm (hn _)) (hn _)]
  rw [← tsum_mul_left]
  congr 1; ext r
  change _ = Φ p * (tripleWeight a r * phase (differences L _ _ _ p))
  rw [← phase_product]
  unfold tripleWeight
  ring

end Exchange

abbrev ZetaZero := ↥zetaZeroConfig.carrier

private theorem zetaZero_countable : Countable ZetaZero := by
  apply Set.countable_coe_iff.mpr
  have heq : zetaZeroConfig.carrier = ⋃ n : ℕ, zetaZeroConfig.window (-(n : ℝ)) n := by
    ext ρ
    simp only [Set.mem_iUnion, ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hρ
      obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
      exact ⟨n, hρ, by linarith [neg_abs_le ρ.im], (le_abs_self _).trans hn.le⟩
    · rintro ⟨n, hρ, _, _⟩
      exact hρ
  rw [heq]
  exact Set.countable_iUnion fun n => (zetaZeroConfig.window_finite _ _).countable

def heightWeight (k : ℝ → ℂ) (ρ : ZetaZero) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ)

theorem heightWeight_summable_norm {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) : Summable (fun ρ => ‖heightWeight k ρ‖) := by
  exact (summable_norm_iff).2 (WeilEF.EF_lit_zetaZeroConfig k hk hkc).1

theorem shifted_EF (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (b : ℝ) :
    EF.literatureRHS (shift k b) = pairPhaseSum (heightWeight k) (fun ρ => (ρ : ℂ).im) b := by
  rw [← (WeilEF.EF_lit_zetaZeroConfig _ (shift_contDiff hk b) (shift_hasCompactSupport hkc b)).2]
  unfold pairPhaseSum
  congr 1; ext ρ
  have hρ := RH_implies_on_line hRH (show IsNontrivialZero (ρ : ℂ) from ρ.2)
  have hγ : gammaOf (ρ : ℂ) = ((ρ : ℂ).im : ℂ) := by
    apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im, hρ]
  rw [paperFT_shift]
  unfold heightWeight phase
  simp only [hγ, Complex.ofReal_mul, mul_assoc]

/-- Exact ζ three-point identity at fixed height profile and frequency scale.
All three AF right-hand sides are integrated on the same two-frequency plane;
no collision or prime diagonal has yet been removed. -/
theorem zeta_triple_explicit (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (Φ : ℝ × ℝ → ℂ) (hΦ : Integrable Φ) (L : ℝ) :
    (∫ p : ℝ × ℝ, Φ p * (EF.literatureRHS (shift k (L * p.1)) *
      EF.literatureRHS (shift k (L * p.2)) *
      EF.literatureRHS (shift k (-(L * p.1 + L * p.2))))) =
    ∑' r : (ZetaZero × ZetaZero) × ZetaZero, ∫ p : ℝ × ℝ, Φ p * (tripleWeight (heightWeight k) r *
      phase (differences L (r.1.1 : ℂ).im (r.1.2 : ℂ).im (r.2 : ℂ).im p)) := by
  let : Countable ZetaZero := zetaZero_countable
  simp_rw [shifted_EF hRH hk hkc]
  exact integral_product Φ hΦ _ (heightWeight_summable_norm hk hkc) _ L

def gammaWeight (k : ℝ → ℂ) (r : ℝ) : ℂ := paperFT k r * (mu r : ℂ)

theorem gammaWeight_integrable {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) : Integrable (gammaWeight k) :=
  EF.integrable_paperFT_mul_mu hk hkc gammaFacts

def gammaFactor (k : ℝ → ℂ) (b : ℝ) : ℂ := ∫ r, gammaWeight k r * phase (r * b)

theorem gammaFactor_eq (k : ℝ → ℂ) (b : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT (shift k b) r * (EF.gammaBracket r : ℂ) =
      gammaFactor k b := by
  rw [EF.gamma_term, gammaFactor]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [gammaWeight, phase, paperFT_shift, Complex.ofReal_mul, mul_assoc]
  rw [mul_comm (Complex.exp _) (↑(mu r) : ℂ)]

theorem gammaFactor_continuous {k : ℝ → ℂ} (hk : Integrable (gammaWeight k)) :
    Continuous (gammaFactor k) := by
  unfold gammaFactor
  refine continuous_of_dominated (bound := fun r => ‖gammaWeight k r‖) ?_ ?_ hk.norm ?_
  · intro b
    exact hk.aestronglyMeasurable.mul (continuous_phase.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · intro b
    exact Filter.Eventually.of_forall fun r => by rw [norm_mul, norm_phase, mul_one]
  · exact Filter.Eventually.of_forall fun r =>
      continuous_const.mul (continuous_phase.comp (continuous_const.mul continuous_id))

/-- Fubini with a gamma factor and an arbitrary integrable plane amplitude.
The modulus-one phase gives a product majorant independent of the shift. -/
theorem gammaFactor_swap {k : ℝ → ℂ} (hk : Integrable (gammaWeight k))
    (A : ℝ × ℝ → ℂ) (hA : Integrable A) (b : ℝ × ℝ → ℝ) (hb : Continuous b) :
    (∫ p, A p * gammaFactor k (b p)) =
      ∫ r, ∫ p, A p * (gammaWeight k r * phase (r * b p)) := by
  have hP : Integrable (fun z : (ℝ × ℝ) × ℝ => (A z.1 * gammaWeight k z.2) *
      phase (z.2 * b z.1)) (volume.prod volume) := by
    refine (hA.mul_prod hk).mul_bdd (c := 1) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      exact continuous_phase.comp (continuous_snd.mul (hb.comp continuous_fst))
    · exact Filter.Eventually.of_forall fun _ => (norm_phase _).le
  have hF : Integrable (fun z : (ℝ × ℝ) × ℝ => A z.1 *
      (gammaWeight k z.2 * phase (z.2 * b z.1))) (volume.prod volume) := by
    simpa only [mul_assoc] using hP
  simp_rw [gammaFactor, ← EF.cintegral_const_mul]
  exact integral_integral_swap hF

def poleFactor (k : ℝ → ℂ) (b : ℝ) : ℂ :=
  paperFT k (I / 2) * Complex.exp (I * (I / 2) * b) +
    paperFT k (-I / 2) * Complex.exp (I * (-I / 2) * b)

def primeFactor (k : ℝ → ℂ) (B : ℝ) (b : ℝ) : ℂ :=
  - ∑ n ∈ Finset.Ioc 0 ⌊Real.exp B⌋₊,
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (Real.log n - b) + k (-Real.log n - b))

theorem primeFactor_continuous {k : ℝ → ℂ} (hk : Continuous k) (B : ℝ) :
    Continuous (primeFactor k B) := by
  unfold primeFactor
  apply Continuous.neg
  exact continuous_finsetSum _ fun n _ => continuous_const.mul
    ((hk.comp (continuous_const.sub continuous_id)).add (hk.comp (continuous_const.sub continuous_id)))

theorem shifted_support {k : ℝ → ℂ} {K B b : ℝ}
    (hk : ∀ x, k x ≠ 0 → |x| ≤ K) (hb : K + |b| ≤ B) :
    tsupport (shift k b) ⊆ Set.Icc (-B) B := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hxb := hk (x-b) (show k (x-b) ≠ 0 from hx)
  have habs : |x| ≤ B := by
    calc
      |x| = |(x-b)+b| := by rw [sub_add_cancel]
      _ ≤ |x-b| + |b| := abs_add_le _ _
      _ ≤ B := by linarith
  exact abs_le.mp habs

theorem literatureRHS_split {k : ℝ → ℂ} {K B b : ℝ}
    (hk : ∀ x, k x ≠ 0 → |x| ≤ K) (hb : K + |b| ≤ B) :
    EF.literatureRHS (shift k b) = poleFactor k b + primeFactor k B b + gammaFactor k b := by
  unfold EF.literatureRHS poleFactor primeFactor
  rw [gammaFactor_eq, paperFT_shift, paperFT_shift,
    tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp B⌋₊)
      (fun n hn => EF.prime_summand_eq_zero (shifted_support hk hb) hn), sub_eq_add_neg]
  rfl

def frequencyShift (L : ℝ) (i : Fin 3) (p : ℝ × ℝ) : ℝ :=
  ![L * p.1, L * p.2, -(L * p.1 + L * p.2)] i

theorem frequencyShift_continuous (L : ℝ) (i : Fin 3) : Continuous (frequencyShift L i) := by
  fin_cases i <;> unfold frequencyShift <;> dsimp <;> fun_prop

/-- On the three-prime branch, nonzero Fourier cutoffs localize all three
signed logarithms. The signs are encoded in `a`, `b`, `c`, not discarded. -/
theorem localized_prime_logs {k : ℝ → ℂ} {T K L η a b c : ℝ} {p : ℝ × ℝ}
    (hT : 0 < T) (hL : 0 ≤ L) (hk : ∀ x, k x ≠ 0 → |x| ≤ K)
    (hhex : |p.1| + |p.2| + |p.1 + p.2| ≤ 2 - η)
    (ha : dilate k T (a - frequencyShift L 0 p) ≠ 0)
    (hb : dilate k T (b - frequencyShift L 1 p) ≠ 0)
    (hc : dilate k T (c - frequencyShift L 2 p) ≠ 0) :
    |a| + |b| + |c| ≤ (2 - η) * L + 3 * K / T ∧ |a + b + c| ≤ 3 * K / T := by
  have loc (x : ℝ) (i : Fin 3) (hx : dilate k T (x - frequencyShift L i p) ≠ 0) :
      |x - frequencyShift L i p| ≤ K / T := by
    have hn : k (T * (x - frequencyShift L i p)) ≠ 0 := by
      intro he
      exact hx (by simp [dilate, he])
    have hh := hk _ hn
    rw [abs_mul, abs_of_pos hT] at hh
    exact (le_div_iff₀ hT).2 (by simpa only [mul_comm] using hh)
  have hloca := loc a 0 ha
  have hlocb := loc b 1 hb
  have hlocc := loc c 2 hc
  have hbnd (x y : ℝ) : |x| ≤ |x-y| + |y| := by
    simpa only [sub_add_cancel] using abs_add_le (x-y) y
  have hshift : |frequencyShift L 0 p| + |frequencyShift L 1 p| + |frequencyShift L 2 p| ≤
      (2-η)*L := by
    change |L*p.1| + |L*p.2| + |-(L*p.1+L*p.2)| ≤ _
    rw [abs_neg, ← mul_add, abs_mul, abs_mul, abs_mul, abs_of_nonneg hL]
    nlinarith [mul_le_mul_of_nonneg_left hhex hL]
  simp only [mul_div_assoc]
  constructor
  · linarith only [hshift, hloca, hlocb, hlocc,
      hbnd a (frequencyShift L 0 p), hbnd b (frequencyShift L 1 p),
      hbnd c (frequencyShift L 2 p)]
  · have he : a+b+c = (a-frequencyShift L 0 p) + (b-frequencyShift L 1 p) +
        (c-frequencyShift L 2 p) := by
      change _ = (a-L*p.1)+(b-L*p.2)+(c-(-(L*p.1+L*p.2)))
      ring
    rw [he]
    linarith only [hloca, hlocb, hlocc, abs_add_le ((a-frequencyShift L 0 p)+(b-frequencyShift L 1 p))
        (c-frequencyShift L 2 p), abs_add_le (a-frequencyShift L 0 p) (b-frequencyShift L 1 p)]

def factors (k : ℝ → ℂ) (B : ℝ) (j : Fin 3) (b : ℝ) : ℂ :=
  ![poleFactor k b, primeFactor k B b, gammaFactor k b] j

theorem factors_continuous {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (B : ℝ) (j : Fin 3) : Continuous (factors k B j) := by
  fin_cases j
  · change Continuous (poleFactor k)
    unfold poleFactor
    fun_prop
  · exact primeFactor_continuous hk.continuous B
  · exact gammaFactor_continuous (gammaWeight_integrable hk hkc)

/-- A single finite prime cutoff works over the whole support of the frequency
weight. Each of the 27 resulting terms is integrable separately. -/
theorem integral_split_explicit {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {K B L : ℝ} (hkK : ∀ x, k x ≠ 0 → |x| ≤ K)
    {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hcut : ∀ p, Φ p ≠ 0 → ∀ i, K + |frequencyShift L i p| ≤ B) :
    (∫ p, Φ p * (EF.literatureRHS (shift k (frequencyShift L 0 p)) *
      EF.literatureRHS (shift k (frequencyShift L 1 p)) *
      EF.literatureRHS (shift k (frequencyShift L 2 p)))) =
    ∑ js : (Fin 3 × Fin 3) × Fin 3, ∫ p, Φ p *
      (factors k B js.1.1 (frequencyShift L 0 p) * factors k B js.1.2 (frequencyShift L 1 p) *
       factors k B js.2 (frequencyShift L 2 p)) := by
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : Φ p = 0
    · simp [hp]
    · simp_rw [literatureRHS_split hkK (hcut p hp _)]
      simp [Fintype.sum_prod_type, Fin.sum_univ_three, factors]
      ring
  · intro js _
    exact (hΦ.mul (((factors_continuous hk hkc B _).comp (frequencyShift_continuous L _)).mul
      ((factors_continuous hk hkc B _).comp (frequencyShift_continuous L _)) |>.mul
        ((factors_continuous hk hkc B _).comp (frequencyShift_continuous L _)))).integrable_of_hasCompactSupport
      hΦc.mul_right

/-- The ordered smoothed ζ triple sum equals the 27 integrated explicit-formula
terms, at every positive height `T`. This is an exact identity, not an asymptotic. -/
theorem scaled_zeta_triple_explicit_split (hRH : RiemannHypothesis) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {T : ℝ} (hT : 0 < T)
    {K B L : ℝ} (hkK : ∀ x, dilate k T x ≠ 0 → |x| ≤ K)
    {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hcut : ∀ p, Φ p ≠ 0 → ∀ i, K + |frequencyShift L i p| ≤ B) :
    (∑' r : (ZetaZero × ZetaZero) × ZetaZero, ∫ p : ℝ × ℝ, Φ p *
      (tripleWeight (fun ρ : ZetaZero => (zetaZeroConfig.mult ρ : ℂ) *
        paperFT k (gammaOf ρ / (T : ℂ))) r *
      phase (differences L (r.1.1 : ℂ).im (r.1.2 : ℂ).im (r.2 : ℂ).im p))) =
    ∑ js : (Fin 3 × Fin 3) × Fin 3, ∫ p, Φ p *
      (factors (dilate k T) B js.1.1 (frequencyShift L 0 p) *
       factors (dilate k T) B js.1.2 (frequencyShift L 1 p) *
       factors (dilate k T) B js.2 (frequencyShift L 2 p)) := by
  have H := zeta_triple_explicit hRH (dilate_contDiff hk T) (dilate_hasCompactSupport hkc hT)
    Φ (hΦ.integrable_of_hasCompactSupport hΦc) L
  simp only [tripleWeight, heightWeight, paperFT_dilate k hT] at H ⊢
  rw [← H]
  exact integral_split_explicit (dilate_contDiff hk T) (dilate_hasCompactSupport hkc hT) hkK hΦ hΦc hcut

end XiPrime8845.RHTriple

#print axioms XiPrime8845.RHTriple.paperFT_shift
#print axioms XiPrime8845.RHTriple.integral_product
#print axioms XiPrime8845.RHTriple.zeta_triple_explicit
#print axioms XiPrime8845.RHTriple.gammaFactor_swap
#print axioms XiPrime8845.RHTriple.integral_split_explicit
#print axioms XiPrime8845.RHTriple.localized_prime_logs
#print axioms XiPrime8845.RHTriple.scaled_zeta_triple_explicit_split
