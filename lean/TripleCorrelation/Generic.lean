/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
The integration regions are transcribed from the ancillary Julia code of
Gonçalves, de Laat and Leijenhorst, arXiv:2303.01095v2 (ZetaWithPolynomials.tar.xz).
-/
import TripleCorrelation.CheckerInt

/-! # The `x, y` layers of the checker, generic in the coefficient ring

`G3`, `G4` are the two outer (`x`, `y`) integrations of `IntCheck.j3`, `IntCheck.j4`, written
once for an arbitrary coefficient structure `Ops K`.  Three instances are used:

* `K = R1` / `K = R2` (coefficient lists in the inner variables): this is `IntCheck` itself
  (`IntCheck.j3_eq`, `IntCheck.j4_eq`, by `rfl`);
* `K = Int`: the packed checker (`CheckerPack.lean`);
* `K = ℕ × ℕ`: a size bound (coefficient norm, degree), used to prove that packing is lossless.

`Rel` is the logical relation that transports statements between the instances. -/

namespace XiPrime8845.Triple.IntCheck.Gen
open List

variable {K : Type}

def F (o : Ops K) (cv : Int) (κ : K) : List K := [κ, o.ofInt cv]
def E (o : Ops K) (cu cv : Int) (κ : K) : List (List K) := [F o cv κ, [o.ofInt cu]]

def XY (o : Ops K) (L : Int) (r : List (List K)) (xa xb : List K) (ya yb : K) : K :=
  integ o L (integ (polyOps o) L r xa xb) ya yb

def R3 (o : Ops K) (lk : Int → Int → K) (Pt : List (List Int)) : List (List K) :=
  (polyOps (polyOps o)).mul ((polyOps (polyOps o)).mul
    (evalBiv (polyOps (polyOps o)) Pt (E o 1 0 (lk 0 0)) (E o 0 1 (lk 0 0)))
    (evalBiv (polyOps (polyOps o)) Pt (E o 1 0 (lk 1 0)) (E o 0 1 (lk (-1) 0))))
    (E o 0 0 (lk 1 (-2)))

def G3 (o : Ops K) (lk : Int → Int → K) (L : Int) (Pt : List (List Int)) : K × K :=
  (o.add (XY o L (R3 o lk Pt) (F o (-1) (lk 0 (-1))) (F o 0 (lk (-1) 1)) (lk 1 (-1)) (lk 0 0))
    (o.add (XY o L (R3 o lk Pt) (F o 0 (lk 0 (-1))) (F o 0 (lk (-1) 1)) (lk 0 0) (lk 1 0))
      (XY o L (R3 o lk Pt) (F o 0 (lk 0 (-1))) (F o (-1) (lk 0 1)) (lk 1 0) (lk 0 1))),
   XY o L (R3 o lk Pt) (F o 0 (lk 0 (-1))) (F o 0 (lk (-1) 1)) (lk 1 (-1)) (lk 0 1))

def Q (o : Ops K) (lk : Int → Int → Int → K) (Pt : List (List Int)) (zc : Bool) :
    List (List K) :=
  (polyOps (polyOps o)).mul ((polyOps (polyOps o)).mul
    (evalBiv (polyOps (polyOps o)) Pt (E o 1 0 (lk 0 0 0)) (E o 0 1 (lk 0 0 0)))
    (evalBiv (polyOps (polyOps o)) Pt
      (if zc then E o 1 0 (lk (-1) 0 0) else E o 1 0 (lk 0 (-1) 0))
      (if zc then E o 0 1 (lk 0 (-1) 0) else E o 0 1 (lk (-1) 0 0))))
    (if zc then E o 0 0 (lk 0 1 0) else E o 0 0 (lk 1 0 0))

def G4 (o : Ops K) (lk : Int → Int → Int → K) (L : Int) (Pt : List (List Int)) :
    K × K × K × K :=
  (XY o L (Q o lk Pt true) (F o 0 (lk 0 0 (-1))) (F o 0 (lk 1 0 1)) (lk 0 1 (-1)) (lk 0 0 1),
   XY o L (Q o lk Pt true) (F o (-1) (lk 1 1 (-1))) (F o (-1) (lk 0 0 1)) (lk 0 1 (-1)) (lk 0 0 1),
   o.add (XY o L (Q o lk Pt false) (F o 0 (lk 0 0 (-1))) (F o (-1) (lk 0 0 1)) (lk 1 1 0) (lk 0 0 1))
    (o.add (XY o L (Q o lk Pt false) (F o (-1) (lk 1 1 (-1))) (F o (-1) (lk 0 0 1))
        (lk 0 (-1) 0) (lk 1 1 0))
      (XY o L (Q o lk Pt false) (F o (-1) (lk 1 1 (-1))) (F o 0 (lk 0 1 1))
        (lk 1 0 (-1)) (lk 0 (-1) 0))),
   o.add (XY o L (Q o lk Pt false) (F o 0 (lk 0 0 (-1))) (F o (-1) (lk 0 0 1)) (lk 0 (-1) 0) (lk 0 0 1))
    (o.add (XY o L (Q o lk Pt false) (F o 0 (lk 0 0 (-1))) (F o 0 (lk 0 1 1)) (lk 1 1 0) (lk 0 (-1) 0))
      (XY o L (Q o lk Pt false) (F o (-1) (lk 1 1 (-1))) (F o 0 (lk 0 1 1))
        (lk 1 0 (-1)) (lk 1 1 0))))

end Gen

theorem j3_eq (L : Int) (Pt : List (List Int)) :
    j3 L Pt = integ intOps L (Gen.G3 o1 lin1 L Pt).1 0 1
      + integ intOps L (Gen.G3 o1 lin1 L Pt).2 1 2 := rfl

theorem j4_eq (L : Int) (Pt : List (List Int)) :
    j4 L Pt =
      integ intOps L (integ o1 L (Gen.G4 o2 lin2 L Pt).1 (lin1 (-1) 0) (lin1 0 (-1))) 1 2
      + integ intOps L (integ o1 L (Gen.G4 o2 lin2 L Pt).2.1 (lin1 (-1) 1) (lin1 0 0)) 1 2
      + integ intOps L (integ o1 L (Gen.G4 o2 lin2 L Pt).2.2.1 (lin1 (-2) 0) (lin1 (-1) 1)) (-1) 0
      + integ intOps L (integ o1 L (Gen.G4 o2 lin2 L Pt).2.2.2 (lin1 (-1) 0) (lin1 (-2) 0)) (-1) 0 :=
  rfl

namespace Gen
open List

/-! ## Logical relation -/

structure Rel {A B : Type} (R : A → B → Prop) (oa : Ops A) (ob : Ops B) : Prop where
  zero : R oa.zero ob.zero
  add : ∀ {a a' b b'}, R a b → R a' b' → R (oa.add a a') (ob.add b b')
  neg : ∀ {a b}, R a b → R (oa.neg a) (ob.neg b)
  mul : ∀ {a a' b b'}, R a b → R a' b' → R (oa.mul a a') (ob.mul b b')
  smul : ∀ (c : Int) {a b}, R a b → R (oa.smul c a) (ob.smul c b)
  ofInt : ∀ c : Int, R (oa.ofInt c) (ob.ofInt c)

variable {A B : Type} {R : A → B → Prop} {oa : Ops A} {ob : Ops B}

theorem padd_rel (h : Rel R oa ob) : ∀ {p p'} {q q'}, Forall₂ R p p' → Forall₂ R q q' →
    Forall₂ R (padd oa p q) (padd ob p' q') := by
  intro p p' q q' hp
  induction hp generalizing q q' with
  | nil => intro hq; simpa [padd] using hq
  | cons hab hpp ih =>
    intro hq
    cases hq with
    | nil => simpa [padd] using Forall₂.cons hab hpp
    | cons hcd hqq => simp only [padd]; exact Forall₂.cons (h.add hab hcd) (ih hqq)

theorem map_rel {f : A → A} {g : B → B} (hf : ∀ {a b}, R a b → R (f a) (g b)) :
    ∀ {q q'}, Forall₂ R q q' → Forall₂ R (q.map f) (q'.map g) := by
  intro q q' hq
  induction hq with
  | nil => exact Forall₂.nil
  | cons hab _ ih => exact Forall₂.cons (hf hab) ih

theorem pmul_rel (h : Rel R oa ob) : ∀ {p p'} {q q'}, Forall₂ R p p' → Forall₂ R q q' →
    Forall₂ R (pmul oa p q) (pmul ob p' q') := by
  intro p p' q q' hp hq
  induction hp with
  | nil => simp [pmul]
  | cons hab _ ih =>
    simp only [pmul]
    exact padd_rel h (map_rel (fun hx => h.mul hab hx) hq) (Forall₂.cons h.zero ih)

theorem Rel.list (h : Rel R oa ob) : Rel (Forall₂ R) (polyOps oa) (polyOps ob) where
  zero := Forall₂.nil
  add := padd_rel h
  neg := map_rel (fun hx => h.neg hx)
  mul := pmul_rel h
  smul := fun c => map_rel (fun hx => h.smul c hx)
  ofInt := fun c => Forall₂.cons (h.ofInt c) Forall₂.nil

theorem horner_rel (h : Rel R oa ob) {p p'} {a b} (hp : Forall₂ R p p') (hab : R a b) :
    R (horner oa p a) (horner ob p' b) := by
  induction hp with
  | nil => exact h.zero
  | cons hc _ ih => exact h.add hc (h.mul hab ih)

theorem antiAux_rel (h : Rel R oa ob) (L : Int) {p p'} (hp : Forall₂ R p p') :
    ∀ k, Forall₂ R (antiAux oa L k p) (antiAux ob L k p') := by
  induction hp with
  | nil => intro k; exact Forall₂.nil
  | cons hc _ ih => intro k; exact Forall₂.cons (h.smul _ hc) (ih (k + 1))

theorem integ_rel (h : Rel R oa ob) (L : Int) {p p'} {a b a' b'} (hp : Forall₂ R p p')
    (ha : R a a') (hb : R b b') : R (integ oa L p a b) (integ ob L p' a' b') :=
  h.add (horner_rel h (Forall₂.cons h.zero (antiAux_rel h L hp 0)) hb)
    (h.neg (horner_rel h (Forall₂.cons h.zero (antiAux_rel h L hp 0)) ha))

theorem evalBiv_rel (h : Rel R oa ob) (P : List (List Int)) {X Y X' Y'} (hX : R X X')
    (hY : R Y Y') : R (evalBiv oa P X Y) (evalBiv ob P X' Y') := by
  induction P with
  | nil => exact h.zero
  | cons row P ih =>
    refine h.add ?_ (h.mul hX ih)
    induction row with
    | nil => exact h.zero
    | cons c row ihr => exact h.add (h.ofInt c) (h.mul hY ihr)

theorem F_rel (h : Rel R oa ob) (cv : Int) {κ κ'} (hk : R κ κ') :
    Forall₂ R (F oa cv κ) (F ob cv κ') :=
  Forall₂.cons hk (Forall₂.cons (h.ofInt cv) Forall₂.nil)

theorem E_rel (h : Rel R oa ob) (cu cv : Int) {κ κ'} (hk : R κ κ') :
    Forall₂ (Forall₂ R) (E oa cu cv κ) (E ob cu cv κ') :=
  Forall₂.cons (F_rel h cv hk) (Forall₂.cons (Forall₂.cons (h.ofInt cu) Forall₂.nil) Forall₂.nil)

theorem XY_rel (h : Rel R oa ob) (L : Int) {r r'} {xa xb xa' xb'} {ya yb ya' yb'}
    (hr : Forall₂ (Forall₂ R) r r') (hxa : Forall₂ R xa xa') (hxb : Forall₂ R xb xb')
    (hya : R ya ya') (hyb : R yb yb') : R (XY oa L r xa xb ya yb) (XY ob L r' xa' xb' ya' yb') :=
  integ_rel h L (integ_rel h.list L hr hxa hxb) hya hyb

theorem R3_rel (h : Rel R oa ob) {lk : Int → Int → A} {lk' : Int → Int → B}
    (hk : ∀ cd c0, R (lk cd c0) (lk' cd c0)) (Pt : List (List Int)) :
    Forall₂ (Forall₂ R) (R3 oa lk Pt) (R3 ob lk' Pt) :=
  h.list.list.mul (h.list.list.mul
    (evalBiv_rel h.list.list Pt (E_rel h 1 0 (hk _ _)) (E_rel h 0 1 (hk _ _)))
    (evalBiv_rel h.list.list Pt (E_rel h 1 0 (hk _ _)) (E_rel h 0 1 (hk _ _))))
    (E_rel h 0 0 (hk _ _))

theorem G3_rel (h : Rel R oa ob) {lk : Int → Int → A} {lk' : Int → Int → B}
    (hk : ∀ cd c0, R (lk cd c0) (lk' cd c0)) (L : Int) (Pt : List (List Int)) :
    R (G3 oa lk L Pt).1 (G3 ob lk' L Pt).1 ∧ R (G3 oa lk L Pt).2 (G3 ob lk' L Pt).2 := by
  have r := R3_rel h hk Pt
  exact ⟨h.add (XY_rel h L r (F_rel h _ (hk _ _)) (F_rel h _ (hk _ _)) (hk _ _) (hk _ _))
      (h.add (XY_rel h L r (F_rel h _ (hk _ _)) (F_rel h _ (hk _ _)) (hk _ _) (hk _ _))
        (XY_rel h L r (F_rel h _ (hk _ _)) (F_rel h _ (hk _ _)) (hk _ _) (hk _ _))),
    XY_rel h L r (F_rel h _ (hk _ _)) (F_rel h _ (hk _ _)) (hk _ _) (hk _ _)⟩

theorem Q_rel (h : Rel R oa ob) {lk : Int → Int → Int → A} {lk' : Int → Int → Int → B}
    (hk : ∀ cc cd c0, R (lk cc cd c0) (lk' cc cd c0)) (Pt : List (List Int)) (zc : Bool) :
    Forall₂ (Forall₂ R) (Q oa lk Pt zc) (Q ob lk' Pt zc) := by
  cases zc
  · exact h.list.list.mul (h.list.list.mul
      (evalBiv_rel h.list.list Pt (E_rel h 1 0 (hk _ _ _)) (E_rel h 0 1 (hk _ _ _)))
      (evalBiv_rel h.list.list Pt (E_rel h 1 0 (hk _ _ _)) (E_rel h 0 1 (hk _ _ _))))
      (E_rel h 0 0 (hk _ _ _))
  · exact h.list.list.mul (h.list.list.mul
      (evalBiv_rel h.list.list Pt (E_rel h 1 0 (hk _ _ _)) (E_rel h 0 1 (hk _ _ _)))
      (evalBiv_rel h.list.list Pt (E_rel h 1 0 (hk _ _ _)) (E_rel h 0 1 (hk _ _ _))))
      (E_rel h 0 0 (hk _ _ _))

theorem G4_rel (h : Rel R oa ob) {lk : Int → Int → Int → A} {lk' : Int → Int → Int → B}
    (hk : ∀ cc cd c0, R (lk cc cd c0) (lk' cc cd c0)) (L : Int) (Pt : List (List Int)) :
    R (G4 oa lk L Pt).1 (G4 ob lk' L Pt).1 ∧ R (G4 oa lk L Pt).2.1 (G4 ob lk' L Pt).2.1 ∧
    R (G4 oa lk L Pt).2.2.1 (G4 ob lk' L Pt).2.2.1 ∧
    R (G4 oa lk L Pt).2.2.2 (G4 ob lk' L Pt).2.2.2 := by
  have r := Q_rel h hk Pt true
  have s := Q_rel h hk Pt false
  have X : ∀ {r r'}, Forall₂ (Forall₂ R) r r' → ∀ a b c d e f g i j k l m n p : Int,
      R (XY oa L r (F oa a (lk b c d)) (F oa e (lk f g i)) (lk j k l) (lk m n p))
        (XY ob L r' (F ob a (lk' b c d)) (F ob e (lk' f g i)) (lk' j k l) (lk' m n p)) :=
    fun hr _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      XY_rel h L hr (F_rel h _ (hk _ _ _)) (F_rel h _ (hk _ _ _)) (hk _ _ _) (hk _ _ _)
  exact ⟨X r .., X r .., h.add (X s ..) (h.add (X s ..) (X s ..)),
    h.add (X s ..) (h.add (X s ..) (X s ..))⟩

end XiPrime8845.Triple.IntCheck.Gen
