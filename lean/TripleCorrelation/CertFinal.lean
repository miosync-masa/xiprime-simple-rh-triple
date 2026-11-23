/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.Phi0Props
import TripleCorrelation.Nu3Continuity

/-! # The certificate bounds the Fourier-side functional of `Φ₀ = F ⋆ F̃`

`cert_nu3` (degree-independent): for an integer table `P` passing the Boolean checks
`shapeOK`, `degOK`, `symOK` and the gate `IntCheck.gate D N P gn gd`, with `0 < gd`, the function
`Φ₀ ξ = Phi0 (pOf P) ξ` (complex-valued) is continuous, vanishes outside
`|ξ₁|+|ξ₂|+|ξ₁+ξ₂| ≤ 2`, has `mass Φ₀ ≠ 0`, and `(nu3F Φ₀ / mass Φ₀).re ≤ gn/gd`.

`P20_nu3`: the d = 20 instance with `c₂₀ = 77223/1000000`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Sym
open Region Nu3 IntCheck IntCheck.Sem

/-! ## invariance of the table, by a Boolean check -/

def symOK (P : List (List Int)) : Bool :=
  decide (Pack.T2 (IntCheck.o2.add (IntCheck.evalBiv IntCheck.o2 P (IntCheck.lin2 0 1 0) (IntCheck.lin2 1 0 0))
      (IntCheck.o2.neg (IntCheck.evalBiv IntCheck.o2 P (IntCheck.lin2 1 0 0) (IntCheck.lin2 0 1 0)))) = 0)
  && decide (Pack.T2 (IntCheck.o2.add
      (IntCheck.evalBiv IntCheck.o2 P (IntCheck.lin2 1 0 0) (IntCheck.lin2 (-1) (-1) 0))
      (IntCheck.o2.neg (IntCheck.evalBiv IntCheck.o2 P (IntCheck.lin2 1 0 0) (IntCheck.lin2 0 1 0)))) = 0)
  && decide (Pack.T2 (IntCheck.o2.add
      (IntCheck.evalBiv IntCheck.o2 P (IntCheck.lin2 (-1) 0 0) (IntCheck.lin2 0 (-1) 0))
      (IntCheck.o2.neg (IntCheck.evalBiv IntCheck.o2 P (IntCheck.lin2 1 0 0) (IntCheck.lin2 0 1 0)))) = 0)

theorem diff_zero (a b : IntCheck.R2) (h : Pack.T2 (IntCheck.o2.add a (IntCheck.o2.neg b)) = 0)
    (e : ℝ × ℝ × Unit) : lv2.f a e = lv2.f b e := by
  have z := congrFun (lv2.Z _ h) e
  have hh := congrFun (lv2.hom.add (a := a) (a' := IntCheck.o2.neg b) rfl (lv2.hom.neg rfl)) e
  have : lv2.f a e + -(lv2.f b e) = 0 := hh.symm.trans z
  linarith

theorem symOK_sound {P : List (List Int)} (h : symOK P = true) :
    (∀ u : ℝ × ℝ, pOf P (u.2, u.1) = pOf P u) ∧
    (∀ u : ℝ × ℝ, pOf P (u.1, -(u.1 + u.2)) = pOf P u) ∧
    (∀ u : ℝ × ℝ, pOf P (-u.1, -u.2) = pOf P u) := by
  simp only [symOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
  · have := diff_zero _ _ h1 (u.1, (u.2, ()))
    rw [ev_lin2, ev_lin2] at this
    simp only [pOf]
    convert this using 2 <;> push_cast <;> ring
  · have := diff_zero _ _ h2 (u.1, (u.2, ()))
    rw [ev_lin2, ev_lin2] at this
    simp only [pOf]
    convert this using 2 <;> push_cast <;> ring
  · have := diff_zero _ _ h3 (u.1, (u.2, ()))
    rw [ev_lin2, ev_lin2] at this
    simp only [pOf]
    convert this using 2 <;> push_cast <;> ring

/-! ## real to complex -/

theorem nu3F_ofReal (Φ : ℝ × ℝ → ℝ) :
    nu3F (fun ξ => (Φ ξ : ℂ)) = ((nu3R Φ : ℝ) : ℂ) := by
  have e : (∫ ξ : ℝ × ℝ, (K ξ : ℂ) * (Φ ξ : ℂ)) = ((∫ ξ : ℝ × ℝ, K ξ * Φ ξ : ℝ) : ℂ) := by
    have := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure (ℝ × ℝ))) (f := fun ξ => K ξ * Φ ξ)
    exact (integral_congr_ae (Filter.Eventually.of_forall fun ξ => by simp)).trans this
  unfold nu3F lineInt nu3R
  rw [e]
  simp only [← Complex.ofReal_mul, intervalIntegral.integral_ofReal]
  push_cast
  ring

theorem mass_ofReal (Φ : ℝ × ℝ → ℝ) : mass (fun ξ => (Φ ξ : ℂ)) = ((∫ ξ, Φ ξ : ℝ) : ℂ) := by
  unfold mass; exact integral_ofReal

theorem pOf_continuous (P : List (List Int)) : Continuous (pOf P) := PR_continuous P

theorem AR_eq_Aint {p : ℝ × ℝ → ℝ} (hp : Continuous p) : AR (Phi0 p) = Aint p := by
  have hc : Continuous fun z : ℝ => (z - 1) * Phi0 p (-z, z) :=
    (by fun_prop : Continuous fun z : ℝ => z - 1).mul
      ((Phi0_continuous hp).comp (by fun_prop : Continuous fun z : ℝ => (-z, z)))
  unfold AR Aint
  exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1 / 2))
    (hc.intervalIntegrable (1 / 2) 1)).symm

/-- **the certificate theorem**, degree-independent. -/
theorem cert_nu3 {D N : ℕ} {P : List (List Int)} {gn gd : Int} (hs : shapeOK D 0 P = true)
    (hdeg : degOK D N P = true) (hsym : symOK P = true)
    (hg : IntCheck.gate D N P gn gd = true) (hgd : 0 < gd) :
    Continuous (fun ξ => (Phi0 (pOf P) ξ : ℂ)) ∧
    (∀ ξ, (Phi0 (pOf P) ξ : ℂ) ≠ 0 → hexSum ξ ≤ 2) ∧
    mass (fun ξ => (Phi0 (pOf P) ξ : ℂ)) ≠ 0 ∧
    (nu3F (fun ξ => (Phi0 (pOf P) ξ : ℂ)) / mass (fun ξ => (Phi0 (pOf P) ξ : ℂ))).re
      ≤ (gn : ℝ) / gd := by
  have hp := pOf_continuous P
  obtain ⟨s1, s2, s3⟩ := symOK_sound hsym
  have hc := Phi0_continuous hp
  have hsupp : ∀ ξ, Phi0 (pOf P) ξ ≠ 0 → hexSum ξ ≤ 2 := fun ξ => Phi0_supp ξ
  have hinv := Phi0_Inv s1 s2 s3
  have hmass := Phi0_mass hp
  obtain ⟨hm0, hle⟩ := gate_orig hs hdeg hg
  have hm2 : 0 < mF (pOf P) ^ 2 := by positivity
  have hgd' : (0 : ℝ) < gd := by exact_mod_cast hgd
  have hred := nu3R_eq hc hsupp hinv
  rw [hmass, AR_eq_Aint hp] at hred
  have hBR : BR (Phi0 (pOf P)) = Bint (pOf P) := rfl
  rw [hBR] at hred
  have key : nu3R (Phi0 (pOf P)) / mF (pOf P) ^ 2 ≤ (gn : ℝ) / gd := by
    rw [div_le_div_iff₀ hm2 hgd', hred]
    nlinarith [hle]
  refine ⟨Complex.continuous_ofReal.comp hc, fun ξ h => hsupp ξ (by exact_mod_cast h), ?_, ?_⟩
  · rw [mass_ofReal, hmass]
    exact_mod_cast hm2.ne'
  · rw [nu3F_ofReal, mass_ofReal, hmass, ← Complex.ofReal_div, Complex.ofReal_re]
    exact key

end XiPrime8845.Triple.Sym

namespace XiPrime8845.Triple
open IntCheck IntCheck.Sem Region Nu3 XiPrime8845.Triple.Sym

theorem P20i_symOK : symOK P20i = true := by decide +kernel

/-- d = 20: `ν₃`-functional of the certificate function, `c₂₀ = 77223/1000000`. -/
theorem P20_nu3 :
    Continuous (fun ξ => (Phi0 (pOf P20i) ξ : ℂ)) ∧
    (∀ ξ, (Phi0 (pOf P20i) ξ : ℂ) ≠ 0 → hexSum ξ ≤ 2) ∧
    mass (fun ξ => (Phi0 (pOf P20i) ξ : ℂ)) ≠ 0 ∧
    (nu3F (fun ξ => (Phi0 (pOf P20i) ξ : ℂ)) / mass (fun ξ => (Phi0 (pOf P20i) ξ : ℂ))).re
      ≤ 77223 / 1000000 := by
  have := cert_nu3 P20i_shapeOK P20i_degOK' P20i_symOK P20i_gate (by norm_num)
  simpa using this

/-- d = 20, limit form: any quantity bounded along a family converging to the certificate
function (pointwise, uniformly bounded, common bounded support) is bounded by `c₂₀`. -/
theorem P20_limit {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    {Φ : ι → ℝ × ℝ → ℂ} {M R x : ℝ} (hc : ∀ n, Continuous (Φ n)) (hM : ∀ n ξ, ‖Φ n ξ‖ ≤ M)
    (hsupp : ∀ n ξ, ξ ∉ Metric.closedBall (0 : ℝ × ℝ) R → Φ n ξ = 0)
    (hlim : ∀ ξ, Filter.Tendsto (fun n => Φ n ξ) l (nhds (Phi0 (pOf P20i) ξ : ℂ)))
    (hx : ∀ᶠ n in l, x ≤ (nu3F (Φ n) / mass (Φ n)).re) : x ≤ 77223 / 1000000 :=
  le_trans (le_ratio_of_eventually_le hc hM hsupp hlim P20_nu3.2.2.1 hx) P20_nu3.2.2.2

end XiPrime8845.Triple

#print axioms XiPrime8845.Triple.P20_limit
#print axioms XiPrime8845.Triple.Sym.cert_nu3
#print axioms XiPrime8845.Triple.P20_nu3
