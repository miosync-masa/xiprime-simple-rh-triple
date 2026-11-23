/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Mathlib

/-! # Continuity of the Fourier-side triple functional under dominated convergence

`nu3F Φ` is the Fourier-side form of `∫ g W₃(x₁,x₂,0)` for `Φ = ĝ`, without any symmetry
assumption on `Φ`:
`Φ(0) − Σ_{3 lines} ∫_{-1}^{1} (1−|u|) Φ(line(u)) du + 2 ∫ K·Φ`,
`K(ξ) = max 0 (1 − (|ξ₁|+|ξ₂|+|ξ₁+ξ₂|)/2)`; `mass Φ = ∫ Φ` is `g(0)`.

That this equals `∫ g W₃`, and that for a 12-fold symmetric `Φ` it equals the expression checked
by the certificate (`2·mass + Φ(0) + 6∫₀¹Φ(x,0)(x−1)dx − 12∫₀¹∫_{−x₂}⁰Φ·x₂`), is a hand
computation and is NOT proved in this file.

Proved here: if `Φ n → Φ₀` pointwise, with a uniform bound and a common bounded support, then
`nu3F (Φ n) / mass (Φ n) → nu3F Φ₀ / mass Φ₀`; hence a strict upper bound for the limit holds
eventually along the family. -/

open MeasureTheory Filter Topology

namespace XiPrime8845.Triple.Nu3

noncomputable section

def K (ξ : ℝ × ℝ) : ℝ := max 0 (1 - (|ξ.1| + |ξ.2| + |ξ.1 + ξ.2|) / 2)

def lineInt (Φ : ℝ × ℝ → ℂ) (ℓ : ℝ → ℝ × ℝ) : ℂ :=
  ∫ u in (-1 : ℝ)..1, ((1 - |u| : ℝ) : ℂ) * Φ (ℓ u)

def nu3F (Φ : ℝ × ℝ → ℂ) : ℂ :=
  Φ (0, 0) - (lineInt Φ (fun u => (u, -u)) + lineInt Φ (fun u => (u, 0))
    + lineInt Φ (fun u => (0, u))) + 2 * ∫ ξ : ℝ × ℝ, (K ξ : ℂ) * Φ ξ

def mass (Φ : ℝ × ℝ → ℂ) : ℂ := ∫ ξ : ℝ × ℝ, Φ ξ

theorem K_continuous : Continuous K := by unfold K; fun_prop

theorem K_nonneg (ξ : ℝ × ℝ) : 0 ≤ K ξ := le_max_left _ _

theorem K_eq_zero_of_not_mem {ξ : ℝ × ℝ} (h : ξ ∉ Metric.closedBall (0 : ℝ × ℝ) 2) : K ξ = 0 := by
  rw [mem_closedBall_zero_iff, Prod.norm_def, not_le, lt_max_iff] at h
  simp only [Real.norm_eq_abs] at h
  have h3 := abs_nonneg (ξ.1 + ξ.2)
  have h1 := abs_nonneg ξ.1
  have h2 := abs_nonneg ξ.2
  unfold K
  apply max_eq_left
  rcases h with h | h <;> linarith

theorem K_hasCompactSupport : HasCompactSupport K :=
  HasCompactSupport.intro (isCompact_closedBall 0 2) fun _ hx => K_eq_zero_of_not_mem hx

theorem K_integrable : Integrable K := K_continuous.integrable_of_hasCompactSupport K_hasCompactSupport

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

theorem lineInt_tendsto {Φ : ι → ℝ × ℝ → ℂ} {Φ₀ : ℝ × ℝ → ℂ} {M : ℝ} {ℓ : ℝ → ℝ × ℝ}
    (hℓ : Continuous ℓ) (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n x, ‖Φ n x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun n => Φ n x) l (𝓝 (Φ₀ x))) :
    Tendsto (fun n => lineInt (Φ n) ℓ) l (𝓝 (lineInt Φ₀ ℓ)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => |M|)
    (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
    intervalIntegrable_const ?_
  · have : Continuous fun u : ℝ => ((1 - |u| : ℝ) : ℂ) * Φ n (ℓ u) := by
      have := (hc n).comp hℓ
      fun_prop
    exact this.aestronglyMeasurable
  · refine Eventually.of_forall fun u hu => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hu
    have h1 : |(1 - |u|)| ≤ 1 := by
      have := abs_nonneg u
      have : |u| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
      rw [abs_le]; constructor <;> linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |(1 - |u|)| * ‖Φ n (ℓ u)‖ ≤ 1 * |M| :=
          mul_le_mul h1 ((hM n _).trans (le_abs_self M)) (norm_nonneg _) zero_le_one
      _ = |M| := one_mul _
  · exact Eventually.of_forall fun u _ => (hlim (ℓ u)).const_mul _

theorem weighted_tendsto {Φ : ι → ℝ × ℝ → ℂ} {Φ₀ : ℝ × ℝ → ℂ} {M : ℝ}
    (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n x, ‖Φ n x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun n => Φ n x) l (𝓝 (Φ₀ x))) :
    Tendsto (fun n => ∫ ξ : ℝ × ℝ, (K ξ : ℂ) * Φ n ξ) l (𝓝 (∫ ξ : ℝ × ℝ, (K ξ : ℂ) * Φ₀ ξ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun ξ => K ξ * |M|)
    (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
    (K_integrable.mul_const _) ?_
  · have : Continuous fun ξ : ℝ × ℝ => (K ξ : ℂ) * Φ n ξ := by
      have := K_continuous
      have := hc n
      fun_prop
    exact this.aestronglyMeasurable
  · refine Eventually.of_forall fun ξ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (K_nonneg ξ)]
    exact mul_le_mul_of_nonneg_left ((hM n ξ).trans (le_abs_self M)) (K_nonneg ξ)
  · exact Eventually.of_forall fun ξ => (hlim ξ).const_mul _

theorem mass_tendsto {Φ : ι → ℝ × ℝ → ℂ} {Φ₀ : ℝ × ℝ → ℂ} {M R : ℝ}
    (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n x, ‖Φ n x‖ ≤ M)
    (hsupp : ∀ n x, x ∉ Metric.closedBall (0 : ℝ × ℝ) R → Φ n x = 0)
    (hlim : ∀ x, Tendsto (fun n => Φ n x) l (𝓝 (Φ₀ x))) :
    Tendsto (fun n => mass (Φ n)) l (𝓝 (mass Φ₀)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    ((Metric.closedBall (0 : ℝ × ℝ) R).indicator fun _ => |M|)
    (Eventually.of_forall fun n => (hc n).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun ξ => ?_)
    ((continuous_const.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall)
    (Eventually.of_forall fun ξ => hlim ξ)
  by_cases hξ : ξ ∈ Metric.closedBall (0 : ℝ × ℝ) R
  · rw [Set.indicator_of_mem hξ]; exact (hM n ξ).trans (le_abs_self M)
  · rw [Set.indicator_of_notMem hξ, hsupp n ξ hξ, norm_zero]

/-- dominated convergence for the triple functional. -/
theorem nu3F_tendsto {Φ : ι → ℝ × ℝ → ℂ} {Φ₀ : ℝ × ℝ → ℂ} {M : ℝ}
    (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n x, ‖Φ n x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun n => Φ n x) l (𝓝 (Φ₀ x))) :
    Tendsto (fun n => nu3F (Φ n)) l (𝓝 (nu3F Φ₀)) :=
  ((hlim (0, 0)).sub (((lineInt_tendsto (by fun_prop) hc hM hlim).add
    (lineInt_tendsto (by fun_prop) hc hM hlim)).add
    (lineInt_tendsto (by fun_prop) hc hM hlim))).add ((weighted_tendsto hc hM hlim).const_mul 2)

/-- the normalised value `ν₃(g)/g(0)` is continuous along the family. -/
theorem ratio_tendsto {Φ : ι → ℝ × ℝ → ℂ} {Φ₀ : ℝ × ℝ → ℂ} {M R : ℝ}
    (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n x, ‖Φ n x‖ ≤ M)
    (hsupp : ∀ n x, x ∉ Metric.closedBall (0 : ℝ × ℝ) R → Φ n x = 0)
    (hlim : ∀ x, Tendsto (fun n => Φ n x) l (𝓝 (Φ₀ x))) (h0 : mass Φ₀ ≠ 0) :
    Tendsto (fun n => nu3F (Φ n) / mass (Φ n)) l (𝓝 (nu3F Φ₀ / mass Φ₀)) :=
  (nu3F_tendsto hc hM hlim).div (mass_tendsto hc hM hsupp hlim) h0

/-- a strict bound for the limit function holds eventually along the family; no rate needed. -/
theorem eventually_ratio_lt {Φ : ι → ℝ × ℝ → ℂ} {Φ₀ : ℝ × ℝ → ℂ} {M R c : ℝ}
    (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n x, ‖Φ n x‖ ≤ M)
    (hsupp : ∀ n x, x ∉ Metric.closedBall (0 : ℝ × ℝ) R → Φ n x = 0)
    (hlim : ∀ x, Tendsto (fun n => Φ n x) l (𝓝 (Φ₀ x))) (h0 : mass Φ₀ ≠ 0)
    (hlt : (nu3F Φ₀ / mass Φ₀).re < c) :
    ∀ᶠ n in l, (nu3F (Φ n) / mass (Φ n)).re < c :=
  ((Complex.continuous_re.tendsto _).comp (ratio_tendsto hc hM hsupp hlim h0)).eventually
    (eventually_lt_nhds hlt)

/-- limit form: a lower bound that holds along the family passes to the limit function.
With `x = limsup M₃/N` and `(nu3F Φ₀ / mass Φ₀).re ≤ c` this gives `x ≤ c` with the same `c`;
no strict inequality and no rate are needed. -/
theorem le_ratio_of_eventually_le [l.NeBot] {Φ : ι → ℝ × ℝ → ℂ} {Φ₀ : ℝ × ℝ → ℂ} {M R x : ℝ}
    (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n x, ‖Φ n x‖ ≤ M)
    (hsupp : ∀ n x, x ∉ Metric.closedBall (0 : ℝ × ℝ) R → Φ n x = 0)
    (hlim : ∀ x, Tendsto (fun n => Φ n x) l (𝓝 (Φ₀ x))) (h0 : mass Φ₀ ≠ 0)
    (hx : ∀ᶠ n in l, x ≤ (nu3F (Φ n) / mass (Φ n)).re) :
    x ≤ (nu3F Φ₀ / mass Φ₀).re :=
  ge_of_tendsto ((Complex.continuous_re.tendsto _).comp (ratio_tendsto hc hM hsupp hlim h0)) hx

end

end XiPrime8845.Triple.Nu3

#print axioms XiPrime8845.Triple.Nu3.eventually_ratio_lt
#print axioms XiPrime8845.Triple.Nu3.le_ratio_of_eventually_le
