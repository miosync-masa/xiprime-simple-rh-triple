/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.GateRegion

/-! # Back to the original coordinates

`H2 = {u | 2u ∈ hexD}` (`mem_H2_iff`: `|u₁|+|u₂|+|u₁+u₂| ≤ 1`), `F = p·1_{H2}` for
`p u = PR P u.1 u.2`, and the autocorrelation `Phi0 p t = ∫ F(u)·F(u − t) du`.

For a table of degree ≤ `D` (`shapeOK`), `P̃(2u) = 2^D·p(u)` (`PR_scale`), and the four integrals
of `GateRegion` become (`I0D_eq`, `I2D_eq`, `J3D_eq`, `J4D_eq`)
`4·2^D·∫F`, `4·4^D·Phi0 0`, `16·4^D·Aint`, `32·4^D·Bint`, with
`Aint = ∫₀¹ (z−1)·Phi0(−z, z) dz` (written as `∫₀^{1/2} + ∫_{1/2}^1`) and
`Bint = ∫_{0 ≤ t₂ ≤ 1, −t₂ ≤ t₁ ≤ 0} t₂·Phi0(t) dt`.
`gate_orig`: the gate gives `(Phi0 0 + 6·Aint − 12·Bint)·gd ≤ (gn − 2·gd)·(∫F)²`, `∫F ≠ 0`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region
open IntCheck IntCheck.Sem

/-! ## scaling of the table -/

def shapeOK (D : ℕ) : ℕ → List (List Int) → Bool
  | _, [] => true
  | i, row :: t => decide (i ≤ D) && decide (row.length ≤ D - i + 1) && shapeOK D (i + 1) t

def rowval (r : List Int) (Y : ℝ) : ℝ :=
  List.foldr (fun (c : Int) (a : ℝ) => (c : ℝ) + Y * a) 0 r

theorem PR_cons (row : List Int) (t : List (List Int)) (X Y : ℝ) :
    PR (row :: t) X Y = rowval row Y + X * PR t X Y := by
  unfold PR IntCheck.evalBiv rowval; rfl

theorem PR_nil (X Y : ℝ) : PR [] X Y = 0 := by unfold PR IntCheck.evalBiv; rfl

theorem rowval_scale (D i : ℕ) (y : ℝ) : ∀ (r : List Int) (j : ℕ), j + r.length ≤ D - i + 1 →
    (2 : ℝ) ^ j * rowval (scaleRow D i j r) (2 * y) = 2 ^ (D - i) * rowval r y := by
  intro r
  induction r with
  | nil => intro j _; simp [scaleRow, rowval]
  | cons c r ih =>
    intro j hj
    simp only [List.length_cons] at hj
    have h1 := ih (j + 1) (by omega)
    have h2 : (2 : ℝ) ^ j * 2 ^ (D - i - j) = 2 ^ (D - i) := by
      rw [← pow_add]; congr 1; omega
    show (2 : ℝ) ^ j * (((c * 2 ^ (D - i - j) : ℤ) : ℝ)
      + 2 * y * rowval (scaleRow D i (j + 1) r) (2 * y)) = 2 ^ (D - i) * ((c : ℝ) + y * rowval r y)
    rw [pow_succ] at h1
    push_cast
    linear_combination (c : ℝ) * h2 + y * h1

theorem PR_scale_aux (D : ℕ) (x y : ℝ) : ∀ (t : List (List Int)) (i : ℕ), shapeOK D i t = true →
    (2 : ℝ) ^ i * PR (scaleTab D i t) (2 * x) (2 * y) = 2 ^ D * PR t x y := by
  intro t
  induction t with
  | nil => intro i _; simp [scaleTab, PR_nil]
  | cons row t ih =>
    intro i h
    simp only [shapeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hi, hlen⟩, ht⟩ := h
    have h1 := ih (i + 1) ht
    have h2 := rowval_scale D i y row 0 (by omega)
    have h3 : (2 : ℝ) ^ i * 2 ^ (D - i) = 2 ^ D := by rw [← pow_add]; congr 1; omega
    show (2 : ℝ) ^ i * PR (scaleRow D i 0 row :: scaleTab D (i + 1) t) (2 * x) (2 * y) = _
    rw [PR_cons, PR_cons]
    rw [pow_succ] at h1
    simp only [pow_zero, one_mul] at h2
    rw [mul_add, h2, ← mul_assoc, h3]
    linear_combination x * h1

/-- `P̃(2u) = 2^D · p(u)`. -/
theorem PR_scale {D : ℕ} {P : List (List Int)} (h : shapeOK D 0 P = true) (x y : ℝ) :
    PR (scaleTab D 0 P) (2 * x) (2 * y) = 2 ^ D * PR P x y := by
  simpa using PR_scale_aux D x y P 0 h

/-! ## original coordinates -/

def H2 : Set (ℝ × ℝ) := {u | (2 : ℝ) • u ∈ hexD}

theorem mem_H2_iff (u : ℝ × ℝ) : u ∈ H2 ↔ |u.1| + |u.2| + |u.1 + u.2| ≤ 1 := by
  show (2 : ℝ) • u ∈ hexD ↔ _
  rw [mem_hexD]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩
    rcases abs_cases u.1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases u.2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rcases abs_cases (u.1 + u.2) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith
  · intro h
    rcases abs_cases u.1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases u.2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rcases abs_cases (u.1 + u.2) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

def pOf (P : List (List Int)) (u : ℝ × ℝ) : ℝ := PR P u.1 u.2

noncomputable def Fof (p : ℝ × ℝ → ℝ) (u : ℝ × ℝ) : ℝ := H2.indicator p u

/-- autocorrelation of `F = p·1_{H2}`. -/
noncomputable def Phi0 (p : ℝ × ℝ → ℝ) (t : ℝ × ℝ) : ℝ := ∫ u, Fof p u * Fof p (u - t)

noncomputable def mF (p : ℝ × ℝ → ℝ) : ℝ := ∫ u, Fof p u

noncomputable def Aint (p : ℝ × ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2), (z - 1) * Phi0 p (-z, z))
    + ∫ z in (1 / 2 : ℝ)..1, (z - 1) * Phi0 p (-z, z)

def TriH : Set (ℝ × ℝ) := {u | (2 : ℝ) • u ∈ Tri}

noncomputable def Bint (p : ℝ × ℝ → ℝ) : ℝ := ∫ u in TriH, u.2 * Phi0 p u

theorem integral_double (f : ℝ × ℝ → ℝ) : ∫ z, f z = 4 * ∫ u, f ((2 : ℝ) • u) := by
  rw [Measure.integral_comp_smul, Module.finrank_prod, Module.finrank_self]
  norm_num
  ring

variable {D : ℕ} {P : List (List Int)}

theorem Pt_two_smul (h : shapeOK D 0 P = true) (u : ℝ × ℝ) :
    PR (scaleTab D 0 P) ((2 : ℝ) • u).1 ((2 : ℝ) • u).2 = 2 ^ D * pOf P u := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  exact PR_scale h u.1 u.2

theorem I0D_eq (h : shapeOK D 0 P = true) : I0D (scaleTab D 0 P) = 4 * 2 ^ D * mF (pOf P) := by
  unfold I0D mF
  rw [← integral_indicator isClosed_hexD.measurableSet, integral_double]
  have e : ∀ u : ℝ × ℝ, hexD.indicator (fun z => PR (scaleTab D 0 P) z.1 z.2) ((2 : ℝ) • u)
      = 2 ^ D * Fof (pOf P) u := by
    intro u
    by_cases hu : u ∈ H2
    · rw [indicator_of_mem (show (2 : ℝ) • u ∈ hexD from hu), Pt_two_smul h]
      simp [Fof, indicator_of_mem hu]
    · rw [indicator_of_notMem (show (2 : ℝ) • u ∉ hexD from hu)]
      simp [Fof, indicator_of_notMem hu]
  simp only [e, integral_const_mul]
  ring

/-- the common pattern of `I2D`, `T3`, `H4`: a shifted product over `hexD ∩ (hexD + (a,b))`. -/
theorem shifted_eq (h : shapeOK D 0 P = true) (a b κ : ℝ) :
    ∫ z in hexD ∩ {z : ℝ × ℝ | (z.1 - a, z.2 - b) ∈ hexD},
        PR (scaleTab D 0 P) z.1 z.2 * PR (scaleTab D 0 P) (z.1 - a) (z.2 - b) * κ
      = 4 * 4 ^ D * (κ * Phi0 (pOf P) (a / 2, b / 2)) := by
  have ms : MeasurableSet (hexD ∩ {z : ℝ × ℝ | (z.1 - a, z.2 - b) ∈ hexD}) :=
    (isClosed_hexD.inter (isClosed_hexD.preimage
      (by fun_prop : Continuous fun z : ℝ × ℝ => (z.1 - a, z.2 - b)))).measurableSet
  rw [← integral_indicator ms, integral_double]
  have e : ∀ u : ℝ × ℝ, (hexD ∩ {z : ℝ × ℝ | (z.1 - a, z.2 - b) ∈ hexD}).indicator
      (fun z => PR (scaleTab D 0 P) z.1 z.2 * PR (scaleTab D 0 P) (z.1 - a) (z.2 - b) * κ)
        ((2 : ℝ) • u)
      = 4 ^ D * κ * (Fof (pOf P) u * Fof (pOf P) (u - (a / 2, b / 2))) := by
    intro u
    have hp : (((2 : ℝ) • u).1 - a, ((2 : ℝ) • u).2 - b) = (2 : ℝ) • (u - (a / 2, b / 2)) := by
      ext <;> simp <;> ring
    have hv : PR (scaleTab D 0 P) (((2 : ℝ) • u).1 - a) (((2 : ℝ) • u).2 - b)
        = 2 ^ D * pOf P (u - (a / 2, b / 2)) := by
      have := Pt_two_smul h (u - (a / 2, b / 2))
      rw [← hp] at this
      exact this
    have hm : (2 : ℝ) • u ∈ hexD ∩ {z : ℝ × ℝ | (z.1 - a, z.2 - b) ∈ hexD}
        ↔ u ∈ H2 ∧ (u - (a / 2, b / 2)) ∈ H2 := by
      show ((2 : ℝ) • u ∈ hexD ∧ (((2 : ℝ) • u).1 - a, ((2 : ℝ) • u).2 - b) ∈ hexD) ↔ _
      rw [hp]; rfl
    by_cases h1 : u ∈ H2 <;> by_cases h2 : (u - (a / 2, b / 2)) ∈ H2
    · rw [indicator_of_mem (hm.2 ⟨h1, h2⟩), Pt_two_smul h, hv]
      simp only [Fof, indicator_of_mem h1, indicator_of_mem h2]
      have : (4 : ℝ) ^ D = 2 ^ D * 2 ^ D := by rw [← mul_pow]; norm_num
      rw [this]; ring
    · rw [indicator_of_notMem (fun hh => h2 (hm.1 hh).2)]
      simp [Fof, indicator_of_notMem h2]
    · rw [indicator_of_notMem (fun hh => h1 (hm.1 hh).1)]
      simp [Fof, indicator_of_notMem h1]
    · rw [indicator_of_notMem (fun hh => h1 (hm.1 hh).1)]
      simp [Fof, indicator_of_notMem h1]
  simp only [e, integral_const_mul]
  unfold Phi0
  ring

theorem I2D_eq (h : shapeOK D 0 P = true) :
    I2D (scaleTab D 0 P) = 4 * 4 ^ D * Phi0 (pOf P) (0, 0) := by
  have := shifted_eq h 0 0 1
  simp only [sub_zero, mul_one, zero_div, one_mul] at this
  rw [← this]
  unfold I2D
  have hs : hexD ∩ {z : ℝ × ℝ | (z.1, z.2) ∈ hexD} = hexD := by ext z; simp
  rw [hs]

theorem T3_eq (h : shapeOK D 0 P = true) (d : ℝ) :
    T3 (scaleTab D 0 P) d = 4 * 4 ^ D * ((d - 2) * Phi0 (pOf P) (-(d / 2), d / 2)) := by
  have := shifted_eq h (-d) d (d - 2)
  simp only [sub_neg_eq_add, neg_div] at this
  rw [← this]
  rfl

theorem H4_eq (h : shapeOK D 0 P = true) (z : ℝ × ℝ) :
    H4 (scaleTab D 0 P) z = 4 * 4 ^ D * (z.2 * Phi0 (pOf P) (z.1 / 2, z.2 / 2)) := by
  rw [← shifted_eq h z.1 z.2 z.2]
  rfl

theorem J3D_eq (h : shapeOK D 0 P = true) :
    J3D (scaleTab D 0 P) = 16 * 4 ^ D * Aint (pOf P) := by
  have key : ∀ a b : ℝ, ∫ d in a..b, T3 (scaleTab D 0 P) d
      = 16 * 4 ^ D * ∫ z in (a / 2)..(b / 2), (z - 1) * Phi0 (pOf P) (-z, z) := by
    intro a b
    have e : ∀ d : ℝ, T3 (scaleTab D 0 P) d
        = (fun z : ℝ => 8 * 4 ^ D * ((z - 1) * Phi0 (pOf P) (-z, z))) (d / 2) := by
      intro d; rw [T3_eq h]; ring
    have hcd := intervalIntegral.integral_comp_div (a := a) (b := b)
      (fun z : ℝ => 8 * 4 ^ D * ((z - 1) * Phi0 (pOf P) (-z, z))) (two_ne_zero' ℝ)
    rw [intervalIntegral.integral_congr (fun d _ => e d), hcd,
      intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  unfold J3D Aint
  rw [key, key]
  norm_num
  ring

theorem J4D_eq (h : shapeOK D 0 P = true) :
    J4D (scaleTab D 0 P) = 32 * 4 ^ D * Bint (pOf P) := by
  unfold J4D Bint
  have mT : MeasurableSet TriH :=
    (isClosed_Tri.preimage (by fun_prop : Continuous fun u : ℝ × ℝ => (2 : ℝ) • u)).measurableSet
  rw [← integral_indicator isClosed_Tri.measurableSet, integral_double,
    ← integral_indicator mT]
  have e : ∀ u : ℝ × ℝ, Tri.indicator (H4 (scaleTab D 0 P)) ((2 : ℝ) • u)
      = 8 * 4 ^ D * TriH.indicator (fun u => u.2 * Phi0 (pOf P) u) u := by
    intro u
    by_cases hu : u ∈ TriH
    · rw [indicator_of_mem (show (2 : ℝ) • u ∈ Tri from hu), indicator_of_mem hu, H4_eq h]
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [show (2 * u.1 / 2, 2 * u.2 / 2) = u by ext <;> simp]
      ring
    · rw [indicator_of_notMem (show (2 : ℝ) • u ∉ Tri from hu), indicator_of_notMem hu]
      ring
  simp only [e, integral_const_mul]
  ring

/-- **the gate in the original coordinates.** -/
theorem gate_orig {N : ℕ} {gn gd : Int} (hs : shapeOK D 0 P = true) (hdeg : degOK D N P = true)
    (hg : IntCheck.gate D N P gn gd = true) :
    mF (pOf P) ≠ 0 ∧
    (Phi0 (pOf P) (0, 0) + 6 * Aint (pOf P) - 12 * Bint (pOf P)) * gd
      ≤ ((gn : ℝ) - 2 * gd) * mF (pOf P) ^ 2 := by
  obtain ⟨h0, hle⟩ := gate_region hdeg hg
  rw [I0D_eq hs] at h0 hle
  rw [I2D_eq hs, J3D_eq hs, J4D_eq hs] at hle
  have hpos : (0 : ℝ) < 16 * 4 ^ D := by positivity
  refine ⟨fun hm => h0 (by rw [hm]; ring), ?_⟩
  have h4 : (4 : ℝ) ^ D = 2 ^ D * 2 ^ D := by rw [← mul_pow]; norm_num
  have : 16 * 4 ^ D * ((Phi0 (pOf P) (0, 0) + 6 * Aint (pOf P) - 12 * Bint (pOf P)) * gd)
      ≤ 16 * 4 ^ D * (((gn : ℝ) - 2 * gd) * mF (pOf P) ^ 2) := by
    calc _ = (4 * (4 * 4 ^ D * Phi0 (pOf P) (0, 0)) + 6 * (16 * 4 ^ D * Aint (pOf P))
            - 6 * (32 * 4 ^ D * Bint (pOf P))) * (gd : ℝ) := by ring
      _ ≤ _ := hle
      _ = _ := by rw [h4]; ring
  exact le_of_mul_le_mul_left this hpos

end XiPrime8845.Triple.Region

namespace XiPrime8845.Triple
open IntCheck IntCheck.Sem Region

theorem P20i_shapeOK : shapeOK 10 0 P20i = true := by decide +kernel

/-- d = 20 in the original coordinates, `c₂₀ = 77223/1000000`. -/
theorem P20_orig :
    mF (pOf P20i) ≠ 0 ∧
    (Phi0 (pOf P20i) (0, 0) + 6 * Aint (pOf P20i) - 12 * Bint (pOf P20i)) * 1000000
      ≤ ((77223 : ℝ) - 2 * 1000000) * mF (pOf P20i) ^ 2 := by
  have := gate_orig P20i_shapeOK P20i_degOK' P20i_gate
  simpa using this

end XiPrime8845.Triple

#print axioms XiPrime8845.Triple.Region.gate_orig
#print axioms XiPrime8845.Triple.P20_orig
