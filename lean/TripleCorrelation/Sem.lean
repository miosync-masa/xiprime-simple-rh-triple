/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Mathlib
import TripleCorrelation.PackSound

/-! # Real semantics of the list checker: `integ` computes interval integrals

A coefficient list over level `A` (with real semantics `f : A → E → ℝ`) denotes the function
`(t, e) ↦ Σ f(p_k)(e)·t^k` (`semL`).  Main results:

* `Lvl.integ_sem`: `f (integ o L p a b) e = L · ∫ t in f a e..f b e, semL f p (t, e)` for
  `L = lcmUpTo N`, as soon as the degree bound `TL ℓ p ≤ N` holds;
* `Lvl.XY_sem`: the same for two nested integrations.

No ordering of the limits is needed (interval integrals are oriented). -/

namespace XiPrime8845.Triple.IntCheck.Sem
open List Gen Pack MeasureTheory

def realOps : Ops ℝ :=
  ⟨0, (· + ·), fun a => -a, (· * ·), fun c x => (c : ℝ) * x, fun c => (c : ℝ)⟩

def fOps (E : Type) : Ops (E → ℝ) :=
  ⟨fun _ => 0, fun φ ψ e => φ e + ψ e, fun φ e => -φ e, fun φ ψ e => φ e * ψ e,
    fun c φ e => (c : ℝ) * φ e, fun c _ => (c : ℝ)⟩

def levR {A : Type} (x : ℝ) (f : A → ℝ) (p : List A) : ℝ :=
  p.foldr (fun c acc => f c + x * acc) 0

@[simp] theorem levR_nil {A : Type} (x : ℝ) (f : A → ℝ) : levR x f [] = 0 := rfl
@[simp] theorem levR_cons {A : Type} (x : ℝ) (f : A → ℝ) (c : A) (p : List A) :
    levR x f (c :: p) = f c + x * levR x f p := rfl

section hom
variable {A : Type} {f : A → ℝ} {oa : Ops A} (x : ℝ)

theorem levR_padd (h : Rel (fun a v => f a = v) oa realOps) :
    ∀ p q : List A, levR x f (padd oa p q) = levR x f p + levR x f q := by
  intro p
  induction p with
  | nil => intro q; simp [padd]
  | cons a p ih =>
    intro q
    cases q with
    | nil => simp [padd]
    | cons b q =>
      have e : f (oa.add a b) = f a + f b := h.add rfl rfl
      simp only [padd, levR_cons, ih, e]; ring

theorem levR_map_mul (h : Rel (fun a v => f a = v) oa realOps) (a : A) :
    ∀ q : List A, levR x f (q.map (oa.mul a)) = f a * levR x f q := by
  intro q
  induction q with
  | nil => simp
  | cons b q ih =>
    have e : f (oa.mul a b) = f a * f b := h.mul rfl rfl
    simp only [List.map_cons, levR_cons, ih, e]; ring

theorem levR_pmul (h : Rel (fun a v => f a = v) oa realOps) :
    ∀ p q : List A, levR x f (pmul oa p q) = levR x f p * levR x f q := by
  intro p q
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    have e : f oa.zero = 0 := h.zero
    simp only [pmul, levR_padd x h, levR_map_mul x h, levR_cons, ih, e]; ring

theorem levR_rel (h : Rel (fun a v => f a = v) oa realOps) :
    Rel (fun p v => levR x f p = v) (polyOps oa) realOps where
  zero := rfl
  add := by rintro p q _ _ rfl rfl; exact levR_padd x h p q
  neg := by
    rintro p _ rfl
    show levR x f (p.map oa.neg) = -levR x f p
    induction p with
    | nil => simp
    | cons a p ih =>
      have e : f (oa.neg a) = -f a := h.neg rfl
      simp only [List.map_cons, levR_cons, ih, e]; ring
  mul := by rintro p q _ _ rfl rfl; exact levR_pmul x h p q
  smul := by
    rintro c p _ rfl
    show levR x f (p.map (oa.smul c)) = (c : ℝ) * levR x f p
    induction p with
    | nil => simp
    | cons a p ih =>
      have e : f (oa.smul c a) = (c : ℝ) * f a := h.smul c rfl
      simp only [List.map_cons, levR_cons, ih, e]; ring
  ofInt := by
    intro c
    have e : f (oa.ofInt c) = (c : ℝ) := h.ofInt c
    show levR x f [oa.ofInt c] = (c : ℝ)
    simp [e]

theorem levR_map (g : A → ℝ) (p : List A) : levR x (fun c : ℝ => c) (p.map g) = levR x g p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [ih]

theorem forall₂_map_selfR (g : A → ℝ) (p : List A) :
    Forall₂ (fun a v => g a = v) p (p.map g) := by
  induction p with
  | nil => exact Forall₂.nil
  | cons a p ih => exact Forall₂.cons rfl ih

end hom

theorem levR_continuous (q : List ℝ) : Continuous fun t : ℝ => levR t (fun c : ℝ => c) q := by
  induction q with
  | nil => exact continuous_const
  | cons c q ih => exact continuous_const.add (continuous_id.mul ih)

/-! ## Exact integration of a real coefficient list -/

theorem integR_aux (L : ℤ) (A B : ℝ) : ∀ (q : List ℝ) (k : ℕ),
    (∀ j, q.getD j 0 = 0 ∨ ((k + j + 1 : ℕ) : ℤ) ∣ L) →
    B ^ (k + 1) * horner realOps (antiAux realOps L k q) B
      - A ^ (k + 1) * horner realOps (antiAux realOps L k q) A
      = (L : ℝ) * ∫ t in A..B, t ^ k * levR t (fun c : ℝ => c) q := by
  intro q
  induction q with
  | nil => intro k _; simp [antiAux, horner, realOps]
  | cons c q ih =>
    intro k H
    have ih' := ih (k + 1) (fun j => by
      have := H (j + 1)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
    have hc : ((L / ((k : ℤ) + 1) : ℤ) : ℝ) * c = (L : ℝ) * (c / ((k : ℝ) + 1)) := by
      rcases H 0 with h0 | h0
      · have : c = 0 := by simpa using h0
        simp [this]
      · have hd : ((k : ℤ) + 1) ∣ L := by simpa using h0
        have hne : (((k : ℤ) + 1 : ℤ) : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          push_cast; exact this.ne'
        rw [Int.cast_div hd hne]; push_cast; ring
    have hcont : Continuous fun t : ℝ => t ^ (k + 1) * levR t (fun c : ℝ => c) q :=
      (continuous_pow _).mul (levR_continuous q)
    have hint : (∫ t in A..B, t ^ k * levR t (fun c : ℝ => c) (c :: q))
        = c * ((B ^ (k + 1) - A ^ (k + 1)) / ((k : ℝ) + 1))
          + ∫ t in A..B, t ^ (k + 1) * levR t (fun c : ℝ => c) q := by
      have e : (fun t : ℝ => t ^ k * levR t (fun c : ℝ => c) (c :: q))
          = fun t => c * t ^ k + t ^ (k + 1) * levR t (fun c : ℝ => c) q := by
        funext t; simp only [levR_cons]; ring
      rw [e, intervalIntegral.integral_add
          (show IntervalIntegrable (fun t : ℝ => c * t ^ k) volume A B from
            (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _)
          (show IntervalIntegrable (fun t : ℝ => t ^ (k + 1) * levR t (fun c : ℝ => c) q)
            volume A B from hcont.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, integral_pow]
    show B ^ (k + 1) * (((L / ((k : ℤ) + 1) : ℤ) : ℝ) * c
          + B * horner realOps (antiAux realOps L (k + 1) q) B)
        - A ^ (k + 1) * (((L / ((k : ℤ) + 1) : ℤ) : ℝ) * c
          + A * horner realOps (antiAux realOps L (k + 1) q) A) = _
    rw [hint, hc]
    linear_combination ih'

theorem integR (L : ℤ) (A B : ℝ) (q : List ℝ)
    (H : ∀ j, q.getD j 0 = 0 ∨ ((j + 1 : ℕ) : ℤ) ∣ L) :
    integ realOps L q A B = (L : ℝ) * ∫ t in A..B, levR t (fun c : ℝ => c) q := by
  have h := integR_aux L A B q 0 (by simpa using H)
  simp only [pow_zero, one_mul, zero_add, pow_one] at h
  rw [← h]
  show (0 + B * horner realOps (antiAux realOps L 0 q) B)
    + -(0 + A * horner realOps (antiAux realOps L 0 q) A) = _
  ring

theorem dvd_lcmUpTo : ∀ (N m : ℕ), 1 ≤ m → m ≤ N → m ∣ lcmUpTo N
  | 0, m, h1, h2 => by omega
  | N + 1, m, h1, h2 => by
    rcases Nat.lt_or_ge m (N + 1) with h | h
    · exact dvd_trans (dvd_lcmUpTo N m h1 (by omega)) (Nat.dvd_lcm_left _ _)
    · have : m = N + 1 := by omega
      subst this; exact Nat.dvd_lcm_right _ _

/-! ## Levels -/

def semL {A E : Type} (f : A → E → ℝ) (p : List A) : ℝ × E → ℝ :=
  fun te => levR te.1 (fun a => f a te.2) p

theorem pt {A E : Type} {f : A → E → ℝ} {o : Ops A}
    (h : Rel (fun a φ => f a = φ) o (fOps E)) (e : E) :
    Rel (fun a (v : ℝ) => f a e = v) o realOps where
  zero := congrFun h.zero e
  add := by rintro a a' _ _ rfl rfl; exact congrFun (h.add rfl rfl) e
  neg := by rintro a _ rfl; exact congrFun (h.neg rfl) e
  mul := by rintro a a' _ _ rfl rfl; exact congrFun (h.mul rfl rfl) e
  smul := by rintro c a _ rfl; exact congrFun (h.smul c rfl) e
  ofInt := fun c => congrFun (h.ofInt c) e

theorem semL_rel {A E : Type} {f : A → E → ℝ} {o : Ops A}
    (h : Rel (fun a φ => f a = φ) o (fOps E)) :
    Rel (fun p ψ => semL f p = ψ) (polyOps o) (fOps (ℝ × E)) where
  zero := rfl
  add := by
    rintro p q _ _ rfl rfl; funext te; exact (levR_rel te.1 (pt h te.2)).add rfl rfl
  neg := by rintro p _ rfl; funext te; exact (levR_rel te.1 (pt h te.2)).neg rfl
  mul := by
    rintro p q _ _ rfl rfl; funext te; exact (levR_rel te.1 (pt h te.2)).mul rfl rfl
  smul := by rintro c p _ rfl; funext te; exact (levR_rel te.1 (pt h te.2)).smul c rfl
  ofInt := by intro c; funext te; exact (levR_rel te.1 (pt h te.2)).ofInt c

/-- a coefficient level: real semantics, a size, and "degree −∞ means zero". -/
structure Lvl (A E : Type) (o : Ops A) where
  f : A → E → ℝ
  ν : A → ℕ
  ℓ : A → ℕ
  hom : Rel (fun a φ => f a = φ) o (fOps E)
  size : Size ν ℓ o
  Z : ∀ a, ℓ a = 0 → f a = fun _ => 0

variable {A E : Type} {o : Ops A}

theorem semL_zero (lv : Lvl A E o) : ∀ p : List A, TL lv.ℓ p = 0 → semL lv.f p = fun _ => 0 := by
  intro p hp
  funext te
  have hz : ∀ c ∈ p, lv.ℓ c = 0 := by simpa using drop_T (ℓ := lv.ℓ) p 0 (le_of_eq hp)
  show levR te.1 (fun a => lv.f a te.2) p = 0
  clear hp
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp [lv.Z a (hz a (by simp)), ih (fun c hc => hz c (by simp [hc]))]

def Lvl.up (w : ℕ) (lv : Lvl A E o) : Lvl (List A) (ℝ × E) (polyOps o) where
  f := semL lv.f
  ν := νL w lv.ν
  ℓ := TL lv.ℓ
  hom := semL_rel lv.hom
  size := lv.size.list w
  Z := semL_zero lv

theorem getD_zero_of_T (lv : Lvl A E o) (e : E) : ∀ (p : List A) (n j : ℕ), TL lv.ℓ p ≤ n →
    n ≤ j → (p.map fun a => lv.f a e).getD j 0 = 0 := by
  intro p
  induction p with
  | nil => intro n j _ _; simp
  | cons a p ih =>
    intro n j hn hj
    simp only [TL_cons] at hn
    have h1 : lv.ℓ a ≤ n := le_trans (le_max_left _ _) hn
    have h2 : sh (TL lv.ℓ p) ≤ n := le_trans (le_max_right _ _) hn
    cases j with
    | zero =>
      have : lv.ℓ a = 0 := by omega
      simp [lv.Z a this]
    | succ j =>
      have h3 : TL lv.ℓ p ≤ n - 1 := by unfold sh at h2; split at h2 <;> omega
      have := ih (n - 1) j h3 (by omega)
      simpa using this

/-- **`integ` computes `L·∫`** (real semantics), given the degree bound. -/
theorem Lvl.integ_sem (lv : Lvl A E o) {N : ℕ} (p : List A) (a b : A)
    (hp : TL lv.ℓ p ≤ N) (e : E) :
    lv.f (integ o (lcmUpTo N : ℤ) p a b) e
      = (lcmUpTo N : ℝ) * ∫ t in lv.f a e..lv.f b e, semL lv.f p (t, e) := by
  have h1 : lv.f (integ o (lcmUpTo N : ℤ) p a b) e
      = integ realOps (lcmUpTo N : ℤ) (p.map fun c => lv.f c e) (lv.f a e) (lv.f b e) :=
    integ_rel (pt lv.hom e) _ (forall₂_map_selfR _ p) rfl rfl
  rw [h1, integR]
  · simp only [levR_map]; push_cast; rfl
  · intro j
    rcases Nat.lt_or_ge j N with hj | hj
    · right; exact_mod_cast dvd_lcmUpTo N (j + 1) (by omega) (by omega)
    · left; exact getD_zero_of_T lv e p N j hp hj

theorem Lvl.integ_ℓ (lv : Lvl A E o) (L : ℤ) (p : List A) {a b : A} (ha : lv.ℓ a ≤ 2)
    (hb : lv.ℓ b ≤ 2) : lv.ℓ (integ o L p a b) ≤ sh (TL lv.ℓ p) :=
  Pack.integ_ℓ lv.size L p ha hb

/-- real-side mirror of `Gen.XY`. -/
noncomputable def XYR {E : Type} (W : ℝ × ℝ × E → ℝ) (xa xb : ℝ × E → ℝ) (ya yb : E → ℝ) :
    E → ℝ :=
  fun e => ∫ y in ya e..yb e, ∫ x in xa (y, e)..xb (y, e), W (x, (y, e))

theorem Lvl.XY_ℓ (lv : Lvl A E o) (L : ℤ) (r : List (List A)) {xa xb : List A} {ya yb : A}
    (hxa : TL lv.ℓ xa ≤ 2) (hxb : TL lv.ℓ xb ≤ 2) (hya : lv.ℓ ya ≤ 2) (hyb : lv.ℓ yb ≤ 2) :
    lv.ℓ (XY o L r xa xb ya yb) ≤ TL (TL lv.ℓ) r + 2 := by
  have h1 : TL lv.ℓ (integ (polyOps o) L r xa xb) ≤ sh (TL (TL lv.ℓ) r) :=
    (lv.up 1).integ_ℓ L r hxa hxb
  have h2 := lv.integ_ℓ L (integ (polyOps o) L r xa xb) hya hyb
  have h3 := sh_mono h1
  have h4 := sh_le (sh (TL (TL lv.ℓ) r))
  have h5 := sh_le (TL (TL lv.ℓ) r)
  exact le_trans h2 (le_trans h3 (by omega))

/-- **two nested integrations.** -/
theorem Lvl.XY_sem (lv : Lvl A E o) {N : ℕ} (r : List (List A)) {xa xb : List A} (ya yb : A)
    (hr : TL (TL lv.ℓ) r + 1 ≤ N) (hxa : TL lv.ℓ xa ≤ 2) (hxb : TL lv.ℓ xb ≤ 2) (e : E) :
    lv.f (XY o (lcmUpTo N : ℤ) r xa xb ya yb) e
      = (lcmUpTo N : ℝ) ^ 2
        * XYR (semL (semL lv.f) r) (semL lv.f xa) (semL lv.f xb) (lv.f ya) (lv.f yb) e := by
  have h1 : TL lv.ℓ (integ (polyOps o) (lcmUpTo N : ℤ) r xa xb) ≤ sh (TL (TL lv.ℓ) r) :=
    (lv.up 1).integ_ℓ (lcmUpTo N : ℤ) r hxa hxb
  have h5 := sh_le (TL (TL lv.ℓ) r)
  unfold XY XYR
  rw [lv.integ_sem _ _ _ (le_trans h1 (by omega)) e]
  have e2 : ∀ y : ℝ, semL lv.f (integ (polyOps o) (lcmUpTo N : ℤ) r xa xb) (y, e)
      = (lcmUpTo N : ℝ) * ∫ x in semL lv.f xa (y, e)..semL lv.f xb (y, e),
          semL (semL lv.f) r (x, (y, e)) :=
    fun y => (lv.up 1).integ_sem r xa xb
      (show TL (TL lv.ℓ) r ≤ N by omega) (y, e)
  simp only [e2, intervalIntegral.integral_const_mul]
  ring

end XiPrime8845.Triple.IntCheck.Sem
