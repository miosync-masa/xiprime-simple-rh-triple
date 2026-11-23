/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import Mathlib.Tactic
import TripleCorrelation.CheckerPack

/-! # The packed checker computes the same integers as the list checker

Main result: `Pack.numDen_eq : Pack.boundCheck g D N P = true → Pack.numDen g D N P = numDen D N P`
(and `Pack.gate_eq`).  No assumption other than the Boolean `boundCheck`. -/

namespace XiPrime8845.Triple.IntCheck.Pack
open List Gen

/-! ## Evaluation (packing) is a homomorphism -/

def lev {A : Type} (x : Int) (f : A → Int) (p : List A) : Int :=
  p.foldr (fun c acc => f c + x * acc) 0

@[simp] theorem lev_nil {A : Type} (x : Int) (f : A → Int) : lev x f [] = 0 := rfl
@[simp] theorem lev_cons {A : Type} (x : Int) (f : A → Int) (c : A) (p : List A) :
    lev x f (c :: p) = f c + x * lev x f p := rfl

theorem relId : Rel (fun (a v : Int) => (fun c : Int => c) a = v) intOps intOps where
  zero := rfl
  add := by rintro _ _ _ _ rfl rfl; rfl
  neg := by rintro _ _ rfl; rfl
  mul := by rintro _ _ _ _ rfl rfl; rfl
  smul := by rintro c _ _ rfl; rfl
  ofInt := fun _ => rfl

section hom
variable {A : Type} {f : A → Int} {oa : Ops A} (x : Int)

theorem lev_padd (h : Rel (fun a v => f a = v) oa intOps) :
    ∀ p q : List A, lev x f (padd oa p q) = lev x f p + lev x f q := by
  intro p
  induction p with
  | nil => intro q; simp [padd]
  | cons a p ih =>
    intro q
    cases q with
    | nil => simp [padd]
    | cons b q =>
      have e : f (oa.add a b) = f a + f b := h.add rfl rfl
      simp only [padd, lev_cons, ih, e]; ring

theorem lev_map_mul (h : Rel (fun a v => f a = v) oa intOps) (a : A) :
    ∀ q : List A, lev x f (q.map (oa.mul a)) = f a * lev x f q := by
  intro q
  induction q with
  | nil => simp
  | cons b q ih =>
    have e : f (oa.mul a b) = f a * f b := h.mul rfl rfl
    simp only [List.map_cons, lev_cons, ih, e]; ring

theorem lev_pmul (h : Rel (fun a v => f a = v) oa intOps) :
    ∀ p q : List A, lev x f (pmul oa p q) = lev x f p * lev x f q := by
  intro p q
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    have e : f oa.zero = 0 := h.zero
    simp only [pmul, lev_padd x h, lev_map_mul x h, lev_cons, ih, e]; ring

theorem lev_rel (h : Rel (fun a v => f a = v) oa intOps) :
    Rel (fun p v => lev x f p = v) (polyOps oa) intOps where
  zero := rfl
  add := by rintro p q _ _ rfl rfl; exact lev_padd x h p q
  neg := by
    rintro p _ rfl
    show lev x f (p.map oa.neg) = -lev x f p
    induction p with
    | nil => simp
    | cons a p ih =>
      have e : f (oa.neg a) = -f a := h.neg rfl
      simp only [List.map_cons, lev_cons, ih, e]; ring
  mul := by rintro p q _ _ rfl rfl; exact lev_pmul x h p q
  smul := by
    rintro c p _ rfl
    show lev x f (p.map (oa.smul c)) = c * lev x f p
    induction p with
    | nil => simp
    | cons a p ih =>
      have e : f (oa.smul c a) = c * f a := h.smul c rfl
      simp only [List.map_cons, lev_cons, ih, e]; ring
  ofInt := by
    intro c
    have e : f (oa.ofInt c) = c := h.ofInt c
    show lev x f [oa.ofInt c] = c
    simp [e]

theorem lev_map (g : A → Int) (p : List A) : lev x (fun c : Int => c) (p.map g) = lev x g p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [ih]

theorem forall₂_map_self (g : A → Int) (p : List A) :
    Forall₂ (fun a v => g a = v) p (p.map g) := by
  induction p with
  | nil => exact Forall₂.nil
  | cons a p ih => exact Forall₂.cons rfl ih

end hom

/-- value of a `d`-polynomial at `d = B`. -/
def ev1 (B : Int) : R1 → Int := lev B (fun c : Int => c)
/-- value of a `(c, d)`-polynomial at `c = Bn`, `d = B`. -/
def ev2 (B Bn : Int) : R2 → Int := lev Bn (ev1 B)

theorem rel1 (B : Int) : Rel (fun p v => ev1 B p = v) o1 intOps := lev_rel B relId
theorem rel2 (B Bn : Int) : Rel (fun p v => ev2 B Bn p = v) o2 intOps := lev_rel Bn (rel1 B)

/-! ## Sizes -/

def sh (x : ℕ) : ℕ := if x = 0 then 0 else x + 1

theorem sh_le (x : ℕ) : sh x ≤ x + 1 := by unfold sh; split <;> omega
theorem le_sh (x : ℕ) : x ≤ sh x := by unfold sh; split <;> omega
theorem sh_mono {x y : ℕ} (h : x ≤ y) : sh x ≤ sh y := by unfold sh; split <;> split <;> omega
theorem dm_mono {x x' y y' : ℕ} (h : x ≤ x') (h' : y ≤ y') : dm x y ≤ dm x' y' := by
  unfold dm; split <;> split <;> omega
theorem dm_two (y : ℕ) : dm 2 y = sh y := by unfold dm sh; split <;> split <;> omega
theorem sh_dm (x y : ℕ) : sh (dm x y) ≤ dm (sh x) y := by
  unfold dm sh; split <;> split <;> split <;> split <;> omega
theorem sh_dm' (x y : ℕ) : sh (dm x y) ≤ dm x (sh y) := by
  unfold dm sh; split <;> split <;> split <;> split <;> omega
theorem dm_max_left (x x' y : ℕ) : max (dm x y) (dm x' y) ≤ dm (max x x') y :=
  max_le (dm_mono (le_max_left _ _) le_rfl) (dm_mono (le_max_right _ _) le_rfl)
theorem dm_max_right (x y y' : ℕ) : max (dm x y) (dm x y') ≤ dm x (max y y') :=
  max_le (dm_mono le_rfl (le_max_left _ _)) (dm_mono le_rfl (le_max_right _ _))

structure Size {A : Type} (ν ℓ : A → ℕ) (o : Ops A) : Prop where
  ν_zero : ν o.zero = 0
  ℓ_zero : ℓ o.zero = 0
  ν_add : ∀ a b, ν (o.add a b) ≤ ν a + ν b
  ℓ_add : ∀ a b, ℓ (o.add a b) ≤ max (ℓ a) (ℓ b)
  ν_neg : ∀ a, ν (o.neg a) ≤ ν a
  ℓ_neg : ∀ a, ℓ (o.neg a) ≤ ℓ a
  ν_mul : ∀ a b, ν (o.mul a b) ≤ ν a * ν b
  ℓ_mul : ∀ a b, ℓ (o.mul a b) ≤ dm (ℓ a) (ℓ b)
  ν_smul : ∀ (c : Int) a, ν (o.smul c a) ≤ c.natAbs * ν a
  ℓ_smul : ∀ (c : Int) a, ℓ (o.smul c a) ≤ ℓ a
  ν_ofInt : ∀ c : Int, ν (o.ofInt c) ≤ c.natAbs
  ℓ_ofInt : ∀ c : Int, ℓ (o.ofInt c) ≤ 1

def νL {A : Type} (w : ℕ) (ν : A → ℕ) (p : List A) : ℕ := p.foldr (fun c acc => ν c + w * acc) 0
def TL {A : Type} (ℓ : A → ℕ) (p : List A) : ℕ := p.foldr (fun c acc => max (ℓ c) (sh acc)) 0

@[simp] theorem νL_nil {A : Type} (w : ℕ) (ν : A → ℕ) : νL w ν [] = 0 := rfl
@[simp] theorem νL_cons {A : Type} (w : ℕ) (ν : A → ℕ) (c : A) (p : List A) :
    νL w ν (c :: p) = ν c + w * νL w ν p := rfl
@[simp] theorem TL_nil {A : Type} (ℓ : A → ℕ) : TL ℓ [] = 0 := rfl
@[simp] theorem TL_cons {A : Type} (ℓ : A → ℕ) (c : A) (p : List A) :
    TL ℓ (c :: p) = max (ℓ c) (sh (TL ℓ p)) := rfl

section size
variable {A : Type} {ν ℓ : A → ℕ} {o : Ops A} (w : ℕ)

theorem νL_padd (h : Size ν ℓ o) : ∀ p q, νL w ν (padd o p q) ≤ νL w ν p + νL w ν q := by
  intro p
  induction p with
  | nil => intro q; simp [padd]
  | cons a p ih =>
    intro q
    cases q with
    | nil => simp [padd]
    | cons b q =>
      simp only [padd, νL_cons]
      have := h.ν_add a b
      have := Nat.mul_le_mul_left w (ih q)
      rw [Nat.mul_add] at this
      omega

theorem νL_map_mul (h : Size ν ℓ o) (a : A) :
    ∀ q, νL w ν (q.map (o.mul a)) ≤ ν a * νL w ν q := by
  intro q
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons, νL_cons]
    have := h.ν_mul a b
    have := Nat.mul_le_mul_left w ih
    nlinarith

theorem νL_pmul (h : Size ν ℓ o) : ∀ p q, νL w ν (pmul o p q) ≤ νL w ν p * νL w ν q := by
  intro p q
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    simp only [pmul, νL_cons]
    have h1 := νL_padd w h (q.map (o.mul a)) (o.zero :: pmul o p q)
    have h2 := νL_map_mul w h a q
    have h3 := Nat.mul_le_mul_left w ih
    simp only [νL_cons, h.ν_zero] at h1
    nlinarith

theorem TL_padd (h : Size ν ℓ o) : ∀ p q, TL ℓ (padd o p q) ≤ max (TL ℓ p) (TL ℓ q) := by
  intro p
  induction p with
  | nil => intro q; simp [padd]
  | cons a p ih =>
    intro q
    cases q with
    | nil => simp [padd]
    | cons b q =>
      simp only [padd, TL_cons]
      have h1 := h.ℓ_add a b
      have h2 := sh_mono (ih q)
      have h3 : sh (max (TL ℓ p) (TL ℓ q)) ≤ max (sh (TL ℓ p)) (sh (TL ℓ q)) := by
        rcases le_total (TL ℓ p) (TL ℓ q) with hh | hh
        · rw [max_eq_right hh]; exact le_max_right _ _
        · rw [max_eq_left hh]; exact le_max_left _ _
      omega

theorem TL_map_mul (h : Size ν ℓ o) (a : A) :
    ∀ q, TL ℓ (q.map (o.mul a)) ≤ dm (ℓ a) (TL ℓ q) := by
  intro q
  induction q with
  | nil => simp [dm]
  | cons b q ih =>
    simp only [List.map_cons, TL_cons]
    refine le_trans ?_ (dm_max_right _ _ _)
    exact max_le_max (h.ℓ_mul a b) (le_trans (sh_mono ih) (sh_dm' _ _))

theorem TL_pmul (h : Size ν ℓ o) : ∀ p q, TL ℓ (pmul o p q) ≤ dm (TL ℓ p) (TL ℓ q) := by
  intro p q
  induction p with
  | nil => simp [pmul, dm]
  | cons a p ih =>
    simp only [pmul, TL_cons]
    refine le_trans (TL_padd h _ _) ?_
    simp only [TL_cons, h.ℓ_zero]
    refine le_trans ?_ (dm_max_left _ _ _)
    refine max_le_max (TL_map_mul h a q) ?_
    exact max_le (Nat.zero_le _) (le_trans (sh_mono ih) (sh_dm _ _))

theorem Size.list (h : Size ν ℓ o) : Size (νL w ν) (TL ℓ) (polyOps o) where
  ν_zero := rfl
  ℓ_zero := rfl
  ν_add := νL_padd w h
  ℓ_add := TL_padd h
  ν_neg := by
    intro p
    show νL w ν (p.map o.neg) ≤ νL w ν p
    induction p with
    | nil => simp
    | cons a p ih =>
      simp only [List.map_cons, νL_cons]
      have := h.ν_neg a
      have := Nat.mul_le_mul_left w ih
      omega
  ℓ_neg := by
    intro p
    show TL ℓ (p.map o.neg) ≤ TL ℓ p
    induction p with
    | nil => simp
    | cons a p ih =>
      simp only [List.map_cons, TL_cons]
      exact max_le_max (h.ℓ_neg a) (sh_mono ih)
  ν_mul := νL_pmul w h
  ℓ_mul := TL_pmul h
  ν_smul := by
    intro c p
    show νL w ν (p.map (o.smul c)) ≤ c.natAbs * νL w ν p
    induction p with
    | nil => simp
    | cons a p ih =>
      simp only [List.map_cons, νL_cons]
      have := h.ν_smul c a
      have := Nat.mul_le_mul_left w ih
      nlinarith
  ℓ_smul := by
    intro c p
    show TL ℓ (p.map (o.smul c)) ≤ TL ℓ p
    induction p with
    | nil => simp
    | cons a p ih =>
      simp only [List.map_cons, TL_cons]
      exact max_le_max (h.ℓ_smul c a) (sh_mono ih)
  ν_ofInt := by
    intro c
    show νL w ν [o.ofInt c] ≤ c.natAbs
    simpa using h.ν_ofInt c
  ℓ_ofInt := by
    intro c
    show TL ℓ [o.ofInt c] ≤ 1
    simpa [sh] using h.ℓ_ofInt c

theorem Size.rel (h : Size ν ℓ o) : Rel (fun a (s : ℕ × ℕ) => ν a ≤ s.1 ∧ ℓ a ≤ s.2) o oAbs where
  zero := ⟨by simp [h.ν_zero], by simp [h.ℓ_zero]⟩
  add := fun ⟨h1, h2⟩ ⟨h3, h4⟩ =>
    ⟨le_trans (h.ν_add _ _) (Nat.add_le_add h1 h3), le_trans (h.ℓ_add _ _) (max_le_max h2 h4)⟩
  neg := fun ⟨h1, h2⟩ => ⟨le_trans (h.ν_neg _) h1, le_trans (h.ℓ_neg _) h2⟩
  mul := fun ⟨h1, h2⟩ ⟨h3, h4⟩ =>
    ⟨le_trans (h.ν_mul _ _) (Nat.mul_le_mul h1 h3), le_trans (h.ℓ_mul _ _) (dm_mono h2 h4)⟩
  smul := fun c _ _ ⟨h1, h2⟩ =>
    ⟨le_trans (h.ν_smul c _) (Nat.mul_le_mul_left _ h1), le_trans (h.ℓ_smul c _) h2⟩
  ofInt := fun c => ⟨h.ν_ofInt c, h.ℓ_ofInt c⟩

theorem mem_ν (hw : 1 ≤ w) {c : A} : ∀ {p : List A}, c ∈ p → ν c ≤ νL w ν p := by
  intro p
  induction p with
  | nil => intro hc; cases hc
  | cons a p ih =>
    intro hc
    simp only [νL_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · omega
    · have := ih hc
      have := Nat.le_mul_of_pos_left (νL w ν p) hw
      omega

theorem mem_T {c : A} : ∀ {p : List A}, c ∈ p → ℓ c ≤ TL ℓ p := by
  intro p
  induction p with
  | nil => intro hc; cases hc
  | cons a p ih =>
    intro hc
    simp only [TL_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left _ _
    · exact le_trans (ih hc) (le_trans (le_sh _) (le_max_right _ _))

theorem drop_T : ∀ (p : List A) (n : ℕ), TL ℓ p ≤ n → ∀ c ∈ p.drop n, ℓ c = 0 := by
  intro p
  induction p with
  | nil => intro n _ c hc; simp at hc
  | cons a p ih =>
    intro n hn c hc
    simp only [TL_cons] at hn
    have h1 : ℓ a ≤ n := le_trans (le_max_left _ _) hn
    have h2 : sh (TL ℓ p) ≤ n := le_trans (le_max_right _ _) hn
    cases n with
    | zero =>
      have h3 : TL ℓ p ≤ 0 := le_trans (le_sh _) h2
      rcases List.mem_cons.1 (by simpa using hc) with rfl | hc'
      · omega
      · exact ih 0 h3 c (by simpa using hc')
    | succ n =>
      have h3 : TL ℓ p ≤ n := by
        unfold sh at h2; split at h2 <;> omega
      exact ih n h3 c (by simpa using hc)

theorem horner_ν (h : Size ν ℓ o) {t : A} (ht : ν t ≤ w) :
    ∀ p, ν (horner o p t) ≤ νL w ν p := by
  intro p
  induction p with
  | nil => exact le_of_eq h.ν_zero
  | cons c p ih =>
    show ν (o.add c (o.mul t (horner o p t))) ≤ _
    have h1 := h.ν_add c (o.mul t (horner o p t))
    have h2 := h.ν_mul t (horner o p t)
    have h3 := Nat.mul_le_mul ht ih
    simp only [νL_cons]
    omega

theorem horner_ℓ (h : Size ν ℓ o) {t : A} (ht : ℓ t ≤ 2) :
    ∀ p, ℓ (horner o p t) ≤ TL ℓ p := by
  intro p
  induction p with
  | nil => exact le_of_eq h.ℓ_zero
  | cons c p ih =>
    show ℓ (o.add c (o.mul t (horner o p t))) ≤ _
    refine le_trans (h.ℓ_add _ _) (max_le_max le_rfl ?_)
    refine le_trans (h.ℓ_mul _ _) ?_
    rw [← dm_two]
    exact dm_mono ht ih

theorem anti_ν (h : Size ν ℓ o) (L : Int) :
    ∀ p k, νL w ν (antiAux o L k p) ≤ L.natAbs * νL w ν p := by
  intro p
  induction p with
  | nil => intro k; simp [antiAux]
  | cons c p ih =>
    intro k
    simp only [antiAux, νL_cons]
    have h1 := h.ν_smul (L / ((k : Int) + 1)) c
    have h2 : (L / ((k : Int) + 1)).natAbs ≤ L.natAbs := Int.natAbs_ediv_le_natAbs _ _
    have h3 := Nat.mul_le_mul_right (ν c) h2
    have h4 := Nat.mul_le_mul_left w (ih (k + 1))
    nlinarith

theorem anti_ℓ (h : Size ν ℓ o) (L : Int) :
    ∀ p k, TL ℓ (antiAux o L k p) ≤ TL ℓ p := by
  intro p
  induction p with
  | nil => intro k; simp [antiAux]
  | cons c p ih =>
    intro k
    simp only [antiAux, TL_cons]
    exact max_le_max (h.ℓ_smul _ c) (sh_mono (ih (k + 1)))

theorem integ_ν (h : Size ν ℓ o) (L : Int) (p : List A) {a b : A} (ha : ν a ≤ w)
    (hb : ν b ≤ w) : ν (integ o L p a b) ≤ 2 * (w * (L.natAbs * νL w ν p)) := by
  show ν (o.add (horner o (o.zero :: antiAux o L 0 p) b)
    (o.neg (horner o (o.zero :: antiAux o L 0 p) a))) ≤ _
  have h1 := h.ν_add (horner o (o.zero :: antiAux o L 0 p) b)
    (o.neg (horner o (o.zero :: antiAux o L 0 p) a))
  have h2 := h.ν_neg (horner o (o.zero :: antiAux o L 0 p) a)
  have h3 := horner_ν w h hb (o.zero :: antiAux o L 0 p)
  have h4 := horner_ν w h ha (o.zero :: antiAux o L 0 p)
  have h5 := Nat.mul_le_mul_left w (anti_ν w h L p 0)
  simp only [νL_cons, h.ν_zero] at h3 h4
  omega

theorem integ_ℓ (h : Size ν ℓ o) (L : Int) (p : List A) {a b : A} (ha : ℓ a ≤ 2)
    (hb : ℓ b ≤ 2) : ℓ (integ o L p a b) ≤ sh (TL ℓ p) := by
  show ℓ (o.add (horner o (o.zero :: antiAux o L 0 p) b)
    (o.neg (horner o (o.zero :: antiAux o L 0 p) a))) ≤ _
  have h3 := horner_ℓ h hb (o.zero :: antiAux o L 0 p)
  have h4 := horner_ℓ h ha (o.zero :: antiAux o L 0 p)
  have h5 := sh_mono (anti_ℓ h L p 0)
  simp only [TL_cons, h.ℓ_zero] at h3 h4
  refine le_trans (h.ℓ_add _ _) (max_le ?_ (le_trans (h.ℓ_neg _) ?_)) <;> omega

end size

def ν0 (c : Int) : ℕ := c.natAbs
def ℓ0 (c : Int) : ℕ := if c = 0 then 0 else 1

theorem size0 : Size ν0 ℓ0 intOps where
  ν_zero := rfl
  ℓ_zero := rfl
  ν_add := fun a b => Int.natAbs_add_le a b
  ℓ_add := by
    intro a b; show ℓ0 (a + b) ≤ _; unfold ℓ0
    split <;> split <;> split <;> omega
  ν_neg := fun a => le_of_eq (Int.natAbs_neg a)
  ℓ_neg := by intro a; show ℓ0 (-a) ≤ _; unfold ℓ0; split <;> split <;> omega
  ν_mul := fun a b => le_of_eq (Int.natAbs_mul a b)
  ℓ_mul := by
    intro a b; show ℓ0 (a * b) ≤ _; unfold ℓ0 dm
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
  ν_smul := fun c a => le_of_eq (Int.natAbs_mul c a)
  ℓ_smul := by
    intro c a; show ℓ0 (c * a) ≤ _; unfold ℓ0
    by_cases ha : a = 0 <;> simp [ha]; split <;> omega
  ν_ofInt := fun _ => le_rfl
  ℓ_ofInt := by intro c; show ℓ0 c ≤ 1; unfold ℓ0; split <;> omega

def ν1 : R1 → ℕ := νL 1 ν0
def T1 : R1 → ℕ := TL ℓ0
def ν2 : R2 → ℕ := νL 2 ν1
def T2 : R2 → ℕ := TL T1

theorem size1 : Size ν1 T1 o1 := size0.list 1
theorem size2 : Size ν2 T2 o2 := size1.list 2

theorem lev_zero (x : Int) : ∀ p : List Int, (∀ c ∈ p, c = 0) → lev x (fun c : Int => c) p = 0 := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons a p ih =>
    intro h
    simp [h a (by simp), ih (fun c hc => h c (by simp [hc]))]

theorem ℓ0_eq_zero {c : Int} (h : ℓ0 c = 0) : c = 0 := by
  unfold ℓ0 at h; split at h <;> simp_all

theorem zero_of_drop_T1 (q : R1) (n : ℕ) (h : T1 q ≤ n) : ∀ c ∈ q.drop n, c = 0 :=
  fun c hc => ℓ0_eq_zero (drop_T q n h c hc)

theorem ev1_eq_zero (B : Int) (q : R1) (h : T1 q = 0) : ev1 B q = 0 :=
  lev_zero B q (by simpa using zero_of_drop_T1 q 0 (le_of_eq h))

/-! ## Reading digits back -/

def normL : ℕ → List Int → List Int
  | 0, _ => []
  | n + 1, p => p.headD 0 :: normL n p.tail

theorem lev_head_tail (x : Int) (p : List Int) :
    lev x (fun c : Int => c) p = p.headD 0 + x * lev x (fun c : Int => c) p.tail := by
  cases p <;> simp

theorem unpack_lev {R h : Int} (hh : 0 < h) (hR : R = 2 * h) :
    ∀ (n : ℕ) (p : List Int), (∀ c ∈ p, -h ≤ c ∧ c < h) →
      unpack R h n (lev R (fun c : Int => c) p + hsum R h n) = normL n p := by
  intro n
  induction n with
  | zero => intro p _; rfl
  | succ n ih =>
    intro p hp
    have hc : -h ≤ p.headD 0 ∧ p.headD 0 < h := by
      cases p with
      | nil => simp; omega
      | cons a p => exact hp a (by simp)
    have ht : ∀ c ∈ p.tail, -h ≤ c ∧ c < h := fun c hc => hp c (List.mem_of_mem_tail hc)
    have hR0 : R ≠ 0 := by omega
    have e : lev R (fun c : Int => c) p + hsum R h (n + 1)
        = (p.headD 0 + h) + R * (lev R (fun c : Int => c) p.tail + hsum R h n) := by
      rw [lev_head_tail R p]; simp only [hsum]; ring
    simp only [unpack, normL]
    rw [e, Int.add_mul_emod_self_left, Int.add_mul_ediv_left _ _ hR0,
      Int.emod_eq_of_lt (by omega) (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega),
      zero_add, ih p.tail ht]
    simp

theorem anti_zero (L t : Int) : ∀ (p : List Int) (k : ℕ), (∀ c ∈ p, c = 0) →
    horner intOps (antiAux intOps L k p) t = 0 := by
  intro p
  induction p with
  | nil => intro k _; rfl
  | cons a p ih =>
    intro k h
    show (L / ((k : Int) + 1)) * a + t * horner intOps (antiAux intOps L (k + 1) p) t = 0
    rw [h a (by simp), ih (k + 1) (fun c hc => h c (by simp [hc]))]; simp

theorem anti_norm (L t : Int) : ∀ (n k : ℕ) (p : List Int), (∀ c ∈ p.drop n, c = 0) →
    horner intOps (antiAux intOps L k (normL n p)) t = horner intOps (antiAux intOps L k p) t := by
  intro n
  induction n with
  | zero => intro k p h; rw [anti_zero L t p k (by simpa using h)]; rfl
  | succ n ih =>
    intro k p h
    cases p with
    | nil =>
      show (L / ((k : Int) + 1)) * 0 + t * horner intOps (antiAux intOps L (k + 1) (normL n [])) t = 0
      rw [ih (k + 1) [] (by simp)]; simp [antiAux, horner, intOps]
    | cons a p =>
      show (L / ((k : Int) + 1)) * a + t * horner intOps (antiAux intOps L (k + 1) (normL n p)) t
        = (L / ((k : Int) + 1)) * a + t * horner intOps (antiAux intOps L (k + 1) p) t
      rw [ih (k + 1) p (by simpa using h)]

theorem integ_norm (L a b : Int) (n : ℕ) (p : List Int) (h : ∀ c ∈ p.drop n, c = 0) :
    integ intOps L (normL n p) a b = integ intOps L p a b := by
  show (0 + b * horner intOps (antiAux intOps L 0 (normL n p)) b)
      + -(0 + a * horner intOps (antiAux intOps L 0 (normL n p)) a)
    = (0 + b * horner intOps (antiAux intOps L 0 p) b)
      + -(0 + a * horner intOps (antiAux intOps L 0 p) a)
  rw [anti_norm L b n 0 p h, anti_norm L a n 0 p h]

theorem pw_pos (m : ℕ) : 0 < pw m := by unfold pw; positivity
theorem pw_succ (m : ℕ) : pw (m + 1) = 2 * pw m := by unfold pw; push_cast; ring
theorem pw_mul (b n : ℕ) : pw (b * n) = pw b ^ n := by unfold pw; push_cast; ring

/-- core statement: digits are read back correctly. -/
theorem integPacked_eq {e n : ℕ} (he : 0 < e) (L a b : Int) (p : List Int)
    (hbal : ∀ c ∈ p, -pw (e - 1) ≤ c ∧ c < pw (e - 1)) (hz : ∀ c ∈ p.drop n, c = 0) :
    integPacked e n L (lev (pw e) (fun c : Int => c) p) a b = integ intOps L p a b := by
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  unfold integPacked
  rw [unpack_lev (pw_pos _) (by simpa using pw_succ e) n p hbal]
  exact integ_norm L a b n p hz

/-- the `d`-integration of a small `d`-polynomial. -/
theorem dstep {b n : ℕ} (hb : 0 < b) (L x y : Int) (q : R1) (hν : 2 * ν1 q < 2 ^ b)
    (hT : T1 q ≤ n) : integPacked b n L (ev1 (pw b) q) x y = integ intOps L q x y := by
  refine integPacked_eq hb L x y q ?_ (zero_of_drop_T1 q n hT)
  intro c hc
  have h1 : c.natAbs ≤ ν1 q := mem_ν (ν := ν0) 1 le_rfl hc
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have h2 : c.natAbs < 2 ^ b := by rw [pow_succ] at hν; omega
  have h3 : ((c.natAbs : ℕ) : Int) < pw b := by unfold pw; exact_mod_cast h2
  simp only [Nat.add_sub_cancel]
  omega

def geo (B : Int) : ℕ → Int
  | 0 => 0
  | n + 1 => 1 + B * geo B n

theorem geo_nonneg {B : Int} (hB : 0 ≤ B) : ∀ n, 0 ≤ geo B n
  | 0 => le_rfl
  | n + 1 => by have := geo_nonneg hB n; simp only [geo]; positivity

theorem geo_eq (B : Int) : ∀ n, (B - 1) * geo B n = B ^ n - 1
  | 0 => by simp [geo]
  | n + 1 => by have := geo_eq B n; simp only [geo]; rw [pow_succ]; linear_combination B * this

theorem abs_lev_le {B M : Int} (hB : 0 ≤ B) (hM : 0 ≤ M) : ∀ (n : ℕ) (q : List Int),
    (∀ c ∈ q, |c| ≤ M) → (∀ c ∈ q.drop n, c = 0) →
    |lev B (fun c : Int => c) q| ≤ M * geo B n := by
  intro n
  induction n with
  | zero => intro q _ hz; rw [lev_zero B q (by simpa using hz)]; simp [geo]
  | succ n ih =>
    intro q hq hz
    cases q with
    | nil => simp only [lev_nil, abs_zero]; exact mul_nonneg hM (geo_nonneg hB _)
    | cons a q =>
      have h1 := ih q (fun c hc => hq c (by simp [hc])) (by simpa using hz)
      have h2 : |a| ≤ M := hq a (by simp)
      have h3 : |a + B * lev B (fun c : Int => c) q| ≤ |a| + B * |lev B (fun c : Int => c) q| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_of_nonneg hB]
      have h4 := mul_le_mul_of_nonneg_left h1 hB
      simp only [lev_cons, geo]
      nlinarith

/-- the `c`-integration of a small `(c, d)`-polynomial. -/
theorem cstep {b n : ℕ} (hb : 0 < b) (hn : 0 < n) (L x y : Int) (a : R2)
    (hν : 2 * ν2 a < 2 ^ b) (hT : T2 a ≤ n) :
    integPacked (b * n) n L (ev2 (pw b) (pw (b * n)) a) x y
      = integ intOps L (a.map (ev1 (pw b))) x y := by
  have he : 0 < b * n := Nat.mul_pos hb hn
  unfold ev2
  rw [← lev_map]
  refine integPacked_eq he L x y _ ?_ ?_
  · intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    have hq1 : ν1 q ≤ ν2 a := mem_ν (ν := ν1) 2 (by norm_num) hq
    have hq2 : T1 q ≤ n := le_trans (mem_T (ℓ := T1) hq) hT
    have hM : ∀ c ∈ q, |c| ≤ ((ν2 a : ℕ) : Int) := by
      intro c hc
      have : c.natAbs ≤ ν1 q := mem_ν (ν := ν0) 1 le_rfl hc
      rw [Int.abs_eq_natAbs]; exact_mod_cast le_trans this hq1
    have hB : (0 : Int) ≤ pw b := le_of_lt (pw_pos b)
    have h1 := abs_lev_le hB (Int.natCast_nonneg (ν2 a)) n q hM (zero_of_drop_T1 q n hq2)
    have h2 := geo_eq (pw b) n
    have h3 := geo_nonneg hB n
    have h4 : 2 * ((ν2 a : ℕ) : Int) + 1 ≤ pw b := by
      unfold pw; exact_mod_cast hν
    have h5 : pw (b * n) = 2 * pw (b * n - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, b * n = m + 1 := ⟨b * n - 1, by omega⟩
      rw [hm, pw_succ]; simp
    rw [pw_mul] at h5
    have h6 : 2 * (((ν2 a : ℕ) : Int) * geo (pw b) n) ≤ (pw b - 1) * geo (pw b) n := by
      nlinarith
    have h7 := abs_le.1 h1
    show -pw (b * n - 1) ≤ ev1 (pw b) q ∧ ev1 (pw b) q < pw (b * n - 1)
    unfold ev1
    constructor <;> omega
  · intro c hc
    rw [← List.map_drop] at hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    exact ev1_eq_zero _ q (drop_T (ℓ := T1) a n hT q hq)

theorem okD_iff {g : Cfg} {s : ℕ × ℕ} (h : okD g s = true) : 2 * s.1 < 2 ^ g.b ∧ s.2 ≤ g.n := by
  simpa [okD] using h

theorem okCD_iff {g : Cfg} {L : Int} {s : ℕ × ℕ} (h : okCD g L s = true) :
    2 * (2 * (2 * (L.natAbs * s.1))) < 2 ^ g.b ∧ 2 * s.1 < 2 ^ g.b ∧ s.2 + 1 ≤ g.n := by
  simpa [okCD, and_assoc] using h

/-- both inner integrations of one `j4` term. -/
theorem cdInt_eq {g : Cfg} (hb : 0 < g.b) (hn : 0 < g.n) (L da db : Int) (a : R2) (ca cb : R1)
    {s : ℕ × ℕ} (hs : ν2 a ≤ s.1 ∧ T2 a ≤ s.2) (hok : okCD g L s = true)
    (hca : ν1 ca ≤ 2 ∧ T1 ca ≤ 2) (hcb : ν1 cb ≤ 2 ∧ T1 cb ≤ 2) :
    cdInt g L (ev2 (pw g.b) (pw (g.b * g.n)) a) (ev1 (pw g.b) ca) (ev1 (pw g.b) cb) da db
      = integ intOps L (integ o1 L a ca cb) da db := by
  obtain ⟨k1, k2, k3⟩ := okCD_iff hok
  unfold cdInt
  rw [cstep hb hn L _ _ a (by omega) (by omega)]
  have e : ev1 (pw g.b) (integ o1 L a ca cb)
      = integ intOps L (a.map (ev1 (pw g.b))) (ev1 (pw g.b) ca) (ev1 (pw g.b) cb) :=
    integ_rel (rel1 (pw g.b)) L (forall₂_map_self _ a) rfl rfl
  rw [← e]
  refine dstep hb L da db _ ?_ ?_
  · have := integ_ν 2 size1 L a hca.1 hcb.1
    have h1 : L.natAbs * ν2 a ≤ L.natAbs * s.1 := Nat.mul_le_mul_left _ hs.1
    show 2 * ν1 (integ o1 L a ca cb) < 2 ^ g.b
    have : ν1 (integ o1 L a ca cb) ≤ 2 * (2 * (L.natAbs * ν2 a)) := this
    omega
  · have := integ_ℓ size1 L a hca.2 hcb.2
    have h2 := sh_le (T2 a)
    show T1 (integ o1 L a ca cb) ≤ g.n
    have : T1 (integ o1 L a ca cb) ≤ sh (T2 a) := this
    omega

theorem size_lin1 (cd c0 : Int) : ν1 (lin1 cd c0) ≤ (absK1 cd c0).1 ∧ T1 (lin1 cd c0) ≤ (absK1 cd c0).2 := by
  refine ⟨by simp [ν1, lin1, absK1, ν0], ?_⟩
  simp only [T1, lin1, absK1, TL_cons, TL_nil, ℓ0, sh]
  split <;> split <;> simp

theorem size_lin2 (cc cd c0 : Int) :
    ν2 (lin2 cc cd c0) ≤ (absK2 cc cd c0).1 ∧ T2 (lin2 cc cd c0) ≤ (absK2 cc cd c0).2 := by
  have h := size_lin1 cd c0
  refine ⟨?_, ?_⟩
  · have : ν2 (lin2 cc cd c0) = ν1 (lin1 cd c0) + 2 * cc.natAbs := by
      simp [ν2, lin2, ν1, ν0]
    rw [this]; simp only [absK1, absK2] at h ⊢; omega
  · have : T2 (lin2 cc cd c0) = max (T1 (lin1 cd c0)) (sh (max (ℓ0 cc) 0)) := by
      simp [T2, lin2, T1, sh]
    rw [this]
    simp only [absK1, absK2] at h ⊢
    refine max_le h.2 ?_
    unfold sh ℓ0; split <;> split <;> simp_all

theorem ev1_lin1 (g : Cfg) (cd c0 : Int) : ev1 (pw g.b) (lin1 cd c0) = lk3 g cd c0 := by
  simp [ev1, lin1, lk3]; ring

theorem ev2_lin2 (g : Cfg) (cc cd c0 : Int) :
    ev2 (pw g.b) (pw (g.b * g.n)) (lin2 cc cd c0) = lk4 g cc cd c0 := by
  simp [ev2, ev1, lin2, lin1, lk4]; ring

theorem j3_eq' {g : Cfg} (L : Int) (Pt : List (List Int)) (hb : 0 < g.b)
    (h1 : okD g (G3 oAbs absK1 L Pt).1 = true) (h2 : okD g (G3 oAbs absK1 L Pt).2 = true) :
    Pack.j3 g L Pt = IntCheck.j3 L Pt := by
  have hom := G3_rel (rel1 (pw g.b)) (lk := lin1) (lk' := lk3 g) (ev1_lin1 g) L Pt
  have sz := G3_rel size1.rel (lk := lin1) (lk' := absK1) size_lin1 L Pt
  rw [IntCheck.j3_eq, Pack.j3, ← hom.1, ← hom.2]
  rw [dstep hb L 0 1 _ (lt_of_le_of_lt (Nat.mul_le_mul_left 2 sz.1.1) (okD_iff h1).1)
      (le_trans sz.1.2 (okD_iff h1).2),
    dstep hb L 1 2 _ (lt_of_le_of_lt (Nat.mul_le_mul_left 2 sz.2.1) (okD_iff h2).1)
      (le_trans sz.2.2 (okD_iff h2).2)]

theorem j4_eq' {g : Cfg} (L : Int) (Pt : List (List Int)) (hb : 0 < g.b) (hn : 0 < g.n)
    (h1 : okCD g L (G4 oAbs absK2 L Pt).1 = true)
    (h2 : okCD g L (G4 oAbs absK2 L Pt).2.1 = true)
    (h3 : okCD g L (G4 oAbs absK2 L Pt).2.2.1 = true)
    (h4 : okCD g L (G4 oAbs absK2 L Pt).2.2.2 = true) :
    Pack.j4 g L Pt = IntCheck.j4 L Pt := by
  have hom := G4_rel (rel2 (pw g.b) (pw (g.b * g.n))) (lk := lin2) (lk' := lk4 g) (ev2_lin2 g) L Pt
  have sz := G4_rel size2.rel (lk := lin2) (lk' := absK2) size_lin2 L Pt
  have lim : ∀ cd c0 : Int, c0.natAbs + cd.natAbs ≤ 2 →
      ν1 (lin1 cd c0) ≤ 2 ∧ T1 (lin1 cd c0) ≤ 2 := fun cd c0 h =>
    ⟨le_trans (size_lin1 cd c0).1 h, (size_lin1 cd c0).2⟩
  rw [IntCheck.j4_eq, Pack.j4, ← hom.1, ← hom.2.1, ← hom.2.2.1, ← hom.2.2.2]
  simp only [← ev1_lin1]
  rw [cdInt_eq hb hn L 1 2 _ _ _ sz.1 h1 (lim _ _ (by decide)) (lim _ _ (by decide)),
    cdInt_eq hb hn L 1 2 _ _ _ sz.2.1 h2 (lim _ _ (by decide)) (lim _ _ (by decide)),
    cdInt_eq hb hn L (-1) 0 _ _ _ sz.2.2.1 h3 (lim _ _ (by decide)) (lim _ _ (by decide)),
    cdInt_eq hb hn L (-1) 0 _ _ _ sz.2.2.2 h4 (lim _ _ (by decide)) (lim _ _ (by decide))]

/-- **Packing is lossless** whenever the Boolean size check passes. -/
theorem numDen_eq {g : Cfg} {D N : ℕ} {P : List (List Int)} (h : boundCheck g D N P = true) :
    Pack.numDen g D N P = IntCheck.numDen D N P := by
  simp only [boundCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, hn⟩, a1⟩, a2⟩, b1⟩, b2⟩, b3⟩, b4⟩ := h
  show (_, _) = (_, _)
  rw [j3_eq' _ _ hb a1 a2, j4_eq' _ _ hb hn b1 b2 b3 b4]

theorem gate_eq {g : Cfg} {D N : ℕ} {P : List (List Int)} (h : boundCheck g D N P = true)
    (gn gd : Int) : Pack.gate g D N P gn gd = IntCheck.gate D N P gn gd := by
  unfold Pack.gate IntCheck.gate; rw [numDen_eq h]

end XiPrime8845.Triple.IntCheck.Pack
