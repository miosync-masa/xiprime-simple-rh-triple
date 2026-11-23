/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.Sem

/-! # The list checker computes iterated real integrals

`i0_real`, `i2_real`, `j3_real`, `j4_real`: each integer computed by `IntCheck` equals a power
of `L = lcmUpTo N` times an explicit iterated interval integral of a real polynomial function,
under a Boolean degree condition on `N` (degree-only run of the integrand, `degQ`, `deg0`).

Limits and integrands are given as semantics of the checker's linear forms; the `@[simp]`
lemmas `lin1_sem`, `lin2_sem`, `F_sem`, `Q_sem`, `R3_sem` turn them into explicit expressions.
Nothing here identifies the union of the pieces with a geometric region. -/

namespace XiPrime8845.Triple.IntCheck.Sem
open List Gen Pack MeasureTheory

/-! ## degree-only abstract run -/

def oDeg : Ops ℕ := ⟨0, max, id, dm, fun _ a => a, fun _ => 1⟩

theorem relDeg {A : Type} {ν ℓ : A → ℕ} {o : Ops A} (h : Size ν ℓ o) :
    Rel (fun a (t : ℕ) => ℓ a ≤ t) o oDeg where
  zero := le_of_eq h.ℓ_zero
  add := fun h1 h2 => le_trans (h.ℓ_add _ _) (max_le_max h1 h2)
  neg := fun h1 => le_trans (h.ℓ_neg _) h1
  mul := fun h1 h2 => le_trans (h.ℓ_mul _ _) (dm_mono h1 h2)
  smul := fun c _ _ h1 => le_trans (h.ℓ_smul c _) h1
  ofInt := fun c => h.ℓ_ofInt c

def Qtop {A : Type} (oo : Ops A) (Pt : List (List Int)) (x y xz yw w : A) : A :=
  oo.mul (oo.mul (evalBiv oo Pt x y) (evalBiv oo Pt xz yw)) w

/-- degree+1 bound of the four-variable integrand. -/
def degQ (Pt : List (List Int)) : ℕ := Qtop oDeg Pt 2 2 2 2 2
/-- degree+1 bound of `P̃` in two variables. -/
def deg0 (Pt : List (List Int)) : ℕ := evalBiv oDeg Pt 2 2

theorem Qtop_ℓ {A : Type} {ν ℓ : A → ℕ} {oo : Ops A} (h : Size ν ℓ oo) (Pt : List (List Int))
    {x y xz yw w : A} (hx : ℓ x ≤ 2) (hy : ℓ y ≤ 2) (hxz : ℓ xz ≤ 2) (hyw : ℓ yw ≤ 2)
    (hw : ℓ w ≤ 2) : ℓ (Qtop oo Pt x y xz yw w) ≤ degQ Pt :=
  (relDeg h).mul ((relDeg h).mul (evalBiv_rel (relDeg h) Pt hx hy)
    (evalBiv_rel (relDeg h) Pt hxz hyw)) hw

/-! ## the concrete levels -/

def f0 : Int → Unit → ℝ := fun c _ => (c : ℝ)

theorem rel0 : Rel (fun a φ => f0 a = φ) intOps (fOps Unit) where
  zero := by funext _; simp [f0, intOps, fOps]
  add := by rintro a b _ _ rfl rfl; funext _; simp [f0, intOps, fOps]
  neg := by rintro a _ rfl; funext _; simp [f0, intOps, fOps]
  mul := by rintro a b _ _ rfl rfl; funext _; simp [f0, intOps, fOps]
  smul := by rintro c a _ rfl; funext _; simp [f0, intOps, fOps]
  ofInt := by intro c; funext _; simp [f0, intOps, fOps]

def lv0 : Lvl Int Unit intOps where
  f := f0
  ν := ν0
  ℓ := ℓ0
  hom := rel0
  size := size0
  Z := by intro a h; funext _; simp [f0, ℓ0_eq_zero h]

def lv1 : Lvl R1 (ℝ × Unit) o1 := lv0.up 1
def lv2 : Lvl R2 (ℝ × ℝ × Unit) o2 := lv1.up 2
def lv3 : Lvl R3 (ℝ × ℝ × ℝ × Unit) o3 := lv2.up 1
def lv4 : Lvl R4 (ℝ × ℝ × ℝ × ℝ × Unit) o4 := lv3.up 1
/-- the two list levels above `R1` (used by `j3`). -/
def lv2' : Lvl (List R1) (ℝ × ℝ × Unit) (polyOps o1) := lv1.up 1
def lv3' : Lvl (List (List R1)) (ℝ × ℝ × ℝ × Unit) (polyOps (polyOps o1)) := lv2'.up 1

/-- `P̃` as a real polynomial function. -/
def PR (Pt : List (List Int)) (X Y : ℝ) : ℝ := evalBiv realOps Pt X Y

section generic
variable {A E : Type} {o : Ops A} (lv : Lvl A E o)

theorem ofInt_sem (c : Int) (e : E) : lv.f (o.ofInt c) e = (c : ℝ) := congrFun (lv.hom.ofInt c) e

@[simp] theorem F_sem (cv : Int) (κ : A) (y : ℝ) (e : E) :
    semL lv.f (F o cv κ) (y, e) = lv.f κ e + cv * y := by
  simp [semL, F, ofInt_sem lv]; ring

@[simp] theorem E_sem (cu cv : Int) (κ : A) (x y : ℝ) (e : E) :
    semL (semL lv.f) (Gen.E o cu cv κ) (x, (y, e)) = lv.f κ e + cv * y + cu * x := by
  have := F_sem lv cv κ y e
  simp only [semL, Gen.E, levR_cons, levR_nil] at this ⊢
  simp [ofInt_sem lv, F]; ring

theorem evalBiv_sem (Pt : List (List Int)) (X Y : A) (e : E) :
    lv.f (evalBiv o Pt X Y) e = PR Pt (lv.f X e) (lv.f Y e) :=
  evalBiv_rel (pt lv.hom e) Pt rfl rfl

theorem F_ℓ (cv : Int) {κ : A} (h : lv.ℓ κ ≤ 2) : TL lv.ℓ (F o cv κ) ≤ 2 := by
  have h1 := lv.size.ℓ_ofInt cv
  simp only [F, TL_cons, TL_nil]
  have : sh (max (lv.ℓ (o.ofInt cv)) (sh 0)) ≤ 2 := by
    have : max (lv.ℓ (o.ofInt cv)) (sh 0) ≤ 1 := max_le h1 (by simp [sh])
    exact le_trans (sh_le _) (by omega)
  exact max_le h this

theorem E_ℓ (cu cv : Int) {κ : A} (h : lv.ℓ κ ≤ 2) : TL (TL lv.ℓ) (Gen.E o cu cv κ) ≤ 2 := by
  have h1 := lv.size.ℓ_ofInt cu
  have h2 := F_ℓ lv cv h
  simp only [Gen.E, TL_cons, TL_nil]
  have : sh (max (max (lv.ℓ (o.ofInt cu)) (sh 0)) (sh 0)) ≤ 2 := by
    have : max (max (lv.ℓ (o.ofInt cu)) (sh 0)) (sh 0) ≤ 1 :=
      max_le (max_le h1 (by simp [sh])) (by simp [sh])
    exact le_trans (sh_le _) (by omega)
  exact max_le h2 this

theorem XYR_const_mul {E' : Type} (k : ℝ) (W : ℝ × ℝ × E' → ℝ) (xa xb : ℝ × E' → ℝ)
    (ya yb : E' → ℝ) (e : E') :
    XYR (fun z => k * W z) xa xb ya yb e = k * XYR W xa xb ya yb e := by
  simp only [XYR, intervalIntegral.integral_const_mul]

end generic

@[simp] theorem lin1_sem (cd c0 : Int) (d : ℝ) (u : Unit) :
    lv1.f (lin1 cd c0) (d, u) = c0 + cd * d := by
  show levR d (fun a => f0 a u) [c0, cd] = _
  simp [f0, mul_comm]

@[simp] theorem lin2_sem (cc cd c0 : Int) (c d : ℝ) (u : Unit) :
    lv2.f (lin2 cc cd c0) (c, (d, u)) = c0 + cd * d + cc * c := by
  show levR c (fun a => lv1.f a (d, u)) [lin1 cd c0, [cc]] = _
  have : lv1.f [cc] (d, u) = cc := by
    show levR d (fun a => f0 a u) [cc] = _
    simp [f0]
  simp [this, mul_comm]

theorem lin1_ℓ (cd c0 : Int) : lv1.ℓ (lin1 cd c0) ≤ 2 := (size_lin1 cd c0).2
theorem lin2_ℓ (cc cd c0 : Int) : lv2.ℓ (lin2 cc cd c0) ≤ 2 := (size_lin2 cc cd c0).2

theorem Q_eq (Pt : List (List Int)) (zc : Bool) :
    Gen.Q o2 lin2 Pt zc = Qtop o4 Pt (Gen.E o2 1 0 (lin2 0 0 0)) (Gen.E o2 0 1 (lin2 0 0 0))
      (if zc then Gen.E o2 1 0 (lin2 (-1) 0 0) else Gen.E o2 1 0 (lin2 0 (-1) 0))
      (if zc then Gen.E o2 0 1 (lin2 0 (-1) 0) else Gen.E o2 0 1 (lin2 (-1) 0 0))
      (if zc then Gen.E o2 0 0 (lin2 0 1 0) else Gen.E o2 0 0 (lin2 1 0 0)) := rfl

theorem Q_ℓ (Pt : List (List Int)) (zc : Bool) : lv4.ℓ (Gen.Q o2 lin2 Pt zc) ≤ degQ Pt := by
  rw [Q_eq]
  cases zc <;>
  exact Qtop_ℓ lv4.size Pt (E_ℓ lv2 _ _ (lin2_ℓ _ _ _)) (E_ℓ lv2 _ _ (lin2_ℓ _ _ _))
    (E_ℓ lv2 _ _ (lin2_ℓ _ _ _)) (E_ℓ lv2 _ _ (lin2_ℓ _ _ _)) (E_ℓ lv2 _ _ (lin2_ℓ _ _ _))

@[simp] theorem Q_sem (Pt : List (List Int)) (zc : Bool) (x y c d : ℝ) (u : Unit) :
    lv4.f (Gen.Q o2 lin2 Pt zc) (x, (y, (c, (d, u))))
      = PR Pt x y * PR Pt (if zc then x - c else x - d) (if zc then y - d else y - c)
          * (if zc then d else c) := by
  rw [Q_eq]
  have hm : ∀ a b : R4, lv4.f (o4.mul a b) (x, (y, (c, (d, u))))
      = lv4.f a (x, (y, (c, (d, u)))) * lv4.f b (x, (y, (c, (d, u)))) :=
    fun a b => congrFun (lv4.hom.mul rfl rfl) _
  have hE : ∀ (cu cv cc cd c0 : Int), lv4.f (Gen.E o2 cu cv (lin2 cc cd c0)) (x, (y, (c, (d, u))))
      = (c0 + cd * d + cc * c) + cv * y + cu * x := by
    intro cu cv cc cd c0
    have := E_sem lv2 cu cv (lin2 cc cd c0) x y (c, (d, u))
    rw [lin2_sem] at this
    exact this
  unfold Qtop
  rw [hm, hm, evalBiv_sem lv4, evalBiv_sem lv4]
  cases zc <;> simp only [hE, if_true, if_false, Bool.false_eq_true] <;> push_cast <;> ring_nf

theorem R3_eq (Pt : List (List Int)) :
    Gen.R3 o1 lin1 Pt = Qtop (polyOps (polyOps o1)) Pt (Gen.E o1 1 0 (lin1 0 0))
      (Gen.E o1 0 1 (lin1 0 0)) (Gen.E o1 1 0 (lin1 1 0)) (Gen.E o1 0 1 (lin1 (-1) 0))
      (Gen.E o1 0 0 (lin1 1 (-2))) := rfl

theorem R3_ℓ (Pt : List (List Int)) : lv3'.ℓ (Gen.R3 o1 lin1 Pt) ≤ degQ Pt := by
  rw [R3_eq]
  exact Qtop_ℓ lv3'.size Pt (E_ℓ lv1 _ _ (lin1_ℓ _ _)) (E_ℓ lv1 _ _ (lin1_ℓ _ _))
    (E_ℓ lv1 _ _ (lin1_ℓ _ _)) (E_ℓ lv1 _ _ (lin1_ℓ _ _)) (E_ℓ lv1 _ _ (lin1_ℓ _ _))

@[simp] theorem R3_sem (Pt : List (List Int)) (x y d : ℝ) (u : Unit) :
    lv3'.f (Gen.R3 o1 lin1 Pt) (x, (y, (d, u)))
      = PR Pt x y * PR Pt (x + d) (y - d) * (d - 2) := by
  rw [R3_eq]
  have hm : ∀ a b : List (List R1), lv3'.f ((polyOps (polyOps o1)).mul a b) (x, (y, (d, u)))
      = lv3'.f a (x, (y, (d, u))) * lv3'.f b (x, (y, (d, u))) :=
    fun a b => congrFun (lv3'.hom.mul rfl rfl) _
  have hE : ∀ (cu cv cd c0 : Int), lv3'.f (Gen.E o1 cu cv (lin1 cd c0)) (x, (y, (d, u)))
      = (c0 + cd * d) + cv * y + cu * x := by
    intro cu cv cd c0
    have := E_sem lv1 cu cv (lin1 cd c0) x y (d, u)
    rw [lin1_sem] at this
    exact this
  unfold Qtop
  rw [hm, hm, evalBiv_sem lv3', evalBiv_sem lv3']
  simp only [hE]
  push_cast
  ring_nf

/-! ## `j4` -/

/-- one `(x, y)`-integrated piece of `j4`, as a function of `(c, d)`. -/
noncomputable def pc (Pt : List (List Int)) (zc : Bool)
    (cy1 a1 b1 c1 cy2 a2 b2 c2 a3 b3 c3 a4 b4 c4 : Int) : ℝ × ℝ × Unit → ℝ :=
  XYR (lv4.f (Gen.Q o2 lin2 Pt zc)) (lv3.f (F o2 cy1 (lin2 a1 b1 c1)))
    (lv3.f (F o2 cy2 (lin2 a2 b2 c2))) (lv2.f (lin2 a3 b3 c3)) (lv2.f (lin2 a4 b4 c4))

/-- the `(c, d)`-integration of a function of `(c, d)`. -/
noncomputable def cdR (W : ℝ × ℝ × Unit → ℝ) (a1 b1 a2 b2 : Int) (da db : ℝ) : ℝ :=
  XYR W (lv1.f (lin1 a1 b1)) (lv1.f (lin1 a2 b2)) (fun _ => da) (fun _ => db) ()

theorem pc_sem (Pt : List (List Int)) {N : ℕ} (hN : degQ Pt + 3 ≤ N) (zc : Bool)
    (cy1 a1 b1 c1 cy2 a2 b2 c2 a3 b3 c3 a4 b4 c4 : Int) :
    lv2.f (XY o2 (lcmUpTo N : ℤ) (Gen.Q o2 lin2 Pt zc) (F o2 cy1 (lin2 a1 b1 c1))
        (F o2 cy2 (lin2 a2 b2 c2)) (lin2 a3 b3 c3) (lin2 a4 b4 c4))
      = (fun e => (lcmUpTo N : ℝ) ^ 2 * pc Pt zc cy1 a1 b1 c1 cy2 a2 b2 c2 a3 b3 c3 a4 b4 c4 e)
    ∧ lv2.ℓ (XY o2 (lcmUpTo N : ℤ) (Gen.Q o2 lin2 Pt zc) (F o2 cy1 (lin2 a1 b1 c1))
        (F o2 cy2 (lin2 a2 b2 c2)) (lin2 a3 b3 c3) (lin2 a4 b4 c4)) ≤ degQ Pt + 2 := by
  have hQ : TL (TL lv2.ℓ) (Gen.Q o2 lin2 Pt zc) ≤ degQ Pt := Q_ℓ Pt zc
  refine ⟨?_, ?_⟩
  · funext e
    exact lv2.XY_sem _ _ _ (by omega) (F_ℓ lv2 _ (lin2_ℓ _ _ _)) (F_ℓ lv2 _ (lin2_ℓ _ _ _)) e
  · have := lv2.XY_ℓ (lcmUpTo N : ℤ) (Gen.Q o2 lin2 Pt zc) (F_ℓ lv2 cy1 (lin2_ℓ a1 b1 c1))
      (F_ℓ lv2 cy2 (lin2_ℓ a2 b2 c2)) (lin2_ℓ a3 b3 c3) (lin2_ℓ a4 b4 c4)
    omega

theorem add3_sem {a b c : R2} {N : ℕ} {t : ℕ} {Wa Wb Wc : ℝ × ℝ × Unit → ℝ}
    (ha : lv2.f a = (fun e => (lcmUpTo N : ℝ) ^ 2 * Wa e) ∧ lv2.ℓ a ≤ t)
    (hb : lv2.f b = (fun e => (lcmUpTo N : ℝ) ^ 2 * Wb e) ∧ lv2.ℓ b ≤ t)
    (hc : lv2.f c = (fun e => (lcmUpTo N : ℝ) ^ 2 * Wc e) ∧ lv2.ℓ c ≤ t) :
    lv2.f (o2.add a (o2.add b c)) = (fun e => (lcmUpTo N : ℝ) ^ 2 * (Wa e + (Wb e + Wc e)))
      ∧ lv2.ℓ (o2.add a (o2.add b c)) ≤ t := by
  refine ⟨?_, ?_⟩
  · have := lv2.hom.add ha.1 (lv2.hom.add hb.1 hc.1)
    rw [this]; funext e
    show (lcmUpTo N : ℝ) ^ 2 * Wa e + ((lcmUpTo N : ℝ) ^ 2 * Wb e + (lcmUpTo N : ℝ) ^ 2 * Wc e) = _
    ring
  · exact le_trans (lv2.size.ℓ_add _ _)
      (max_le ha.2 (le_trans (lv2.size.ℓ_add _ _) (max_le hb.2 hc.2)))

/-- both inner integrations of one `j4` term. -/
theorem term4 {N : ℕ} (a : R2) (W : ℝ × ℝ × Unit → ℝ)
    (ha : lv2.f a = (fun e => (lcmUpTo N : ℝ) ^ 2 * W e) ∧ lv2.ℓ a + 1 ≤ N)
    (a1 b1 a2 b2 da db : Int) :
    ((integ intOps (lcmUpTo N : ℤ) (integ o1 (lcmUpTo N : ℤ) a (lin1 a1 b1) (lin1 a2 b2)) da db
        : ℤ) : ℝ) = (lcmUpTo N : ℝ) ^ 4 * cdR W a1 b1 a2 b2 da db := by
  have h := lv0.XY_sem (N := N) a (xa := lin1 a1 b1) (xb := lin1 a2 b2) da db ha.2
    (lin1_ℓ a1 b1) (lin1_ℓ a2 b2) ()
  have e1 : semL (semL lv0.f) a = lv2.f a := rfl
  rw [e1, ha.1, XYR_const_mul] at h
  unfold cdR
  rw [show (lcmUpTo N : ℝ) ^ 4 = (lcmUpTo N : ℝ) ^ 2 * (lcmUpTo N : ℝ) ^ 2 by ring, mul_assoc]
  exact h

/-- the real expression computed by `j4` (up to the factor `L⁴`). -/
noncomputable def J4R (Pt : List (List Int)) : ℝ :=
  cdR (pc Pt true 0 0 0 (-1) 0 1 0 1 0 1 (-1) 0 0 1) (-1) 0 0 (-1) 1 2
  + cdR (pc Pt true (-1) 1 1 (-1) (-1) 0 0 1 0 1 (-1) 0 0 1) (-1) 1 0 0 1 2
  + cdR (fun e => pc Pt false 0 0 0 (-1) (-1) 0 0 1 1 1 0 0 0 1 e
      + (pc Pt false (-1) 1 1 (-1) (-1) 0 0 1 0 (-1) 0 1 1 0 e
        + pc Pt false (-1) 1 1 (-1) 0 0 1 1 1 0 (-1) 0 (-1) 0 e)) (-2) 0 (-1) 1 (-1) 0
  + cdR (fun e => pc Pt false 0 0 0 (-1) (-1) 0 0 1 0 (-1) 0 0 0 1 e
      + (pc Pt false 0 0 0 (-1) 0 0 1 1 1 1 0 0 (-1) 0 e
        + pc Pt false (-1) 1 1 (-1) 0 0 1 1 1 0 (-1) 1 1 0 e)) (-1) 0 (-2) 0 (-1) 0

theorem j4_real (Pt : List (List Int)) {N : ℕ} (hN : degQ Pt + 3 ≤ N) :
    ((j4 (lcmUpTo N : ℤ) Pt : ℤ) : ℝ) = (lcmUpTo N : ℝ) ^ 4 * J4R Pt := by
  have P := fun zc cy1 a1 b1 c1 cy2 a2 b2 c2 a3 b3 c3 a4 b4 c4 =>
    pc_sem Pt hN zc cy1 a1 b1 c1 cy2 a2 b2 c2 a3 b3 c3 a4 b4 c4
  have up : ∀ {a : R2} {W : ℝ × ℝ × Unit → ℝ},
      (lv2.f a = (fun e => (lcmUpTo N : ℝ) ^ 2 * W e) ∧ lv2.ℓ a ≤ degQ Pt + 2) →
      (lv2.f a = (fun e => (lcmUpTo N : ℝ) ^ 2 * W e) ∧ lv2.ℓ a + 1 ≤ N) :=
    fun h => ⟨h.1, by have := h.2; omega⟩
  rw [j4_eq]
  simp only [G4]
  push_cast
  rw [term4 _ _ (up (P true 0 0 0 (-1) 0 1 0 1 0 1 (-1) 0 0 1)) (-1) 0 0 (-1) 1 2,
    term4 _ _ (up (P true (-1) 1 1 (-1) (-1) 0 0 1 0 1 (-1) 0 0 1)) (-1) 1 0 0 1 2,
    term4 _ _ (up (add3_sem (P false 0 0 0 (-1) (-1) 0 0 1 1 1 0 0 0 1)
      (P false (-1) 1 1 (-1) (-1) 0 0 1 0 (-1) 0 1 1 0)
      (P false (-1) 1 1 (-1) 0 0 1 1 1 0 (-1) 0 (-1) 0))) (-2) 0 (-1) 1 (-1) 0,
    term4 _ _ (up (add3_sem (P false 0 0 0 (-1) (-1) 0 0 1 0 (-1) 0 0 0 1)
      (P false 0 0 0 (-1) 0 0 1 1 1 1 0 0 (-1) 0)
      (P false (-1) 1 1 (-1) 0 0 1 1 1 0 (-1) 1 1 0))) (-1) 0 (-2) 0 (-1) 0]
  unfold J4R
  push_cast
  ring

/-! ## `j3` -/

@[simp] theorem lv0_f (c : Int) (u : Unit) : lv0.f c u = (c : ℝ) := rfl

noncomputable def pc3 (Pt : List (List Int)) (cv1 a1 b1 cv2 a2 b2 a3 b3 a4 b4 : Int) :
    ℝ × Unit → ℝ :=
  XYR (lv3'.f (Gen.R3 o1 lin1 Pt)) (lv2'.f (F o1 cv1 (lin1 a1 b1)))
    (lv2'.f (F o1 cv2 (lin1 a2 b2))) (lv1.f (lin1 a3 b3)) (lv1.f (lin1 a4 b4))

theorem pc3_sem (Pt : List (List Int)) {N : ℕ} (hN : degQ Pt + 3 ≤ N)
    (cv1 a1 b1 cv2 a2 b2 a3 b3 a4 b4 : Int) :
    lv1.f (XY o1 (lcmUpTo N : ℤ) (Gen.R3 o1 lin1 Pt) (F o1 cv1 (lin1 a1 b1))
        (F o1 cv2 (lin1 a2 b2)) (lin1 a3 b3) (lin1 a4 b4))
      = (fun e => (lcmUpTo N : ℝ) ^ 2 * pc3 Pt cv1 a1 b1 cv2 a2 b2 a3 b3 a4 b4 e)
    ∧ lv1.ℓ (XY o1 (lcmUpTo N : ℤ) (Gen.R3 o1 lin1 Pt) (F o1 cv1 (lin1 a1 b1))
        (F o1 cv2 (lin1 a2 b2)) (lin1 a3 b3) (lin1 a4 b4)) ≤ degQ Pt + 2 := by
  have hQ : TL (TL lv1.ℓ) (Gen.R3 o1 lin1 Pt) ≤ degQ Pt := R3_ℓ Pt
  refine ⟨?_, ?_⟩
  · funext e
    exact lv1.XY_sem _ _ _ (by omega) (F_ℓ lv1 _ (lin1_ℓ _ _)) (F_ℓ lv1 _ (lin1_ℓ _ _)) e
  · have := lv1.XY_ℓ (lcmUpTo N : ℤ) (Gen.R3 o1 lin1 Pt) (F_ℓ lv1 cv1 (lin1_ℓ a1 b1))
      (F_ℓ lv1 cv2 (lin1_ℓ a2 b2)) (lin1_ℓ a3 b3) (lin1_ℓ a4 b4)
    omega

theorem add3_gen {A E : Type} {o : Ops A} (lv : Lvl A E o) {a b c : A} {k : ℝ} {t : ℕ}
    {Wa Wb Wc : E → ℝ} (ha : lv.f a = (fun e => k * Wa e) ∧ lv.ℓ a ≤ t)
    (hb : lv.f b = (fun e => k * Wb e) ∧ lv.ℓ b ≤ t)
    (hc : lv.f c = (fun e => k * Wc e) ∧ lv.ℓ c ≤ t) :
    lv.f (o.add a (o.add b c)) = (fun e => k * (Wa e + (Wb e + Wc e)))
      ∧ lv.ℓ (o.add a (o.add b c)) ≤ t := by
  refine ⟨?_, ?_⟩
  · have := lv.hom.add ha.1 (lv.hom.add hb.1 hc.1)
    rw [this]; funext e
    show k * Wa e + (k * Wb e + k * Wc e) = _
    ring
  · exact le_trans (lv.size.ℓ_add _ _)
      (max_le ha.2 (le_trans (lv.size.ℓ_add _ _) (max_le hb.2 hc.2)))

theorem term3 {N : ℕ} (q : R1) (W : ℝ × Unit → ℝ)
    (hq : lv1.f q = (fun e => (lcmUpTo N : ℝ) ^ 2 * W e) ∧ lv1.ℓ q ≤ N) (da db : Int) :
    ((integ intOps (lcmUpTo N : ℤ) q da db : ℤ) : ℝ)
      = (lcmUpTo N : ℝ) ^ 3 * ∫ d in (da : ℝ)..db, W (d, ()) := by
  have h := lv0.integ_sem (N := N) q da db hq.2 ()
  have e1 : semL lv0.f q = lv1.f q := rfl
  simp only [e1, hq.1, lv0_f, intervalIntegral.integral_const_mul] at h
  rw [h]; ring

noncomputable def J3R (Pt : List (List Int)) : ℝ :=
  (∫ d in ((0 : Int) : ℝ)..(1 : Int), (pc3 Pt (-1) 0 (-1) 0 (-1) 1 1 (-1) 0 0 (d, ())
      + (pc3 Pt 0 0 (-1) 0 (-1) 1 0 0 1 0 (d, ()) + pc3 Pt 0 0 (-1) (-1) 0 1 1 0 0 1 (d, ()))))
  + ∫ d in ((1 : Int) : ℝ)..(2 : Int), pc3 Pt 0 0 (-1) 0 (-1) 1 1 (-1) 0 1 (d, ())

theorem j3_real (Pt : List (List Int)) {N : ℕ} (hN : degQ Pt + 3 ≤ N) :
    ((j3 (lcmUpTo N : ℤ) Pt : ℤ) : ℝ) = (lcmUpTo N : ℝ) ^ 3 * J3R Pt := by
  have P := fun cv1 a1 b1 cv2 a2 b2 a3 b3 a4 b4 =>
    pc3_sem Pt hN cv1 a1 b1 cv2 a2 b2 a3 b3 a4 b4
  have A := P (-1) 0 (-1) 0 (-1) 1 1 (-1) 0 0
  have B := P 0 0 (-1) 0 (-1) 1 0 0 1 0
  have C := P 0 0 (-1) (-1) 0 1 1 0 0 1
  have D := P 0 0 (-1) 0 (-1) 1 1 (-1) 0 1
  have hN2 : degQ Pt + 2 ≤ N := by omega
  have S := add3_gen lv1 A B C
  rw [j3_eq]
  simp only [G3]
  push_cast
  rw [term3 _ _ ⟨S.1, le_trans S.2 hN2⟩ 0 1, term3 _ _ ⟨D.1, le_trans D.2 hN2⟩ 1 2]
  unfold J3R
  ring

/-! ## `i0`, `i2` -/

def S0 (Pt : List (List Int)) : ℝ × ℝ × Unit → ℝ := fun z =>
  PR Pt z.1 z.2.1 + (PR Pt (-z.1 - z.2.1) z.1 + PR Pt z.2.1 (-z.1 - z.2.1))

def S2 (Pt : List (List Int)) : ℝ × ℝ × Unit → ℝ := fun z =>
  PR Pt z.1 z.2.1 * PR Pt z.1 z.2.1 + (PR Pt (-z.1 - z.2.1) z.1 * PR Pt (-z.1 - z.2.1) z.1
    + PR Pt z.2.1 (-z.1 - z.2.1) * PR Pt z.2.1 (-z.1 - z.2.1))

/-- the square integration `∫₀¹ dY ∫₋₁⁰ dX` used by `sqint`. -/
noncomputable def sqR (W : ℝ × ℝ × Unit → ℝ) : ℝ :=
  XYR W (lv1.f (lin1 0 (-1))) (lv1.f (lin1 0 0)) (lv0.f 0) (lv0.f 1) ()

theorem ev_lin2 (Pt : List (List Int)) (a1 b1 c1 a2 b2 c2 : Int) (c d : ℝ) (u : Unit) :
    lv2.f (evalBiv o2 Pt (lin2 a1 b1 c1) (lin2 a2 b2 c2)) (c, (d, u))
      = PR Pt (c1 + b1 * d + a1 * c) (c2 + b2 * d + a2 * c) := by
  rw [evalBiv_sem lv2, lin2_sem, lin2_sem]

theorem i0_real (Pt : List (List Int)) {N : ℕ} (hN : deg0 Pt + 1 ≤ N) :
    ((i0 (lcmUpTo N : ℤ) Pt : ℤ) : ℝ) = (lcmUpTo N : ℝ) ^ 2 * sqR (S0 Pt) := by
  have hd : ∀ a1 b1 c1 a2 b2 c2 : Int,
      lv2.ℓ (evalBiv o2 Pt (lin2 a1 b1 c1) (lin2 a2 b2 c2)) ≤ deg0 Pt := fun _ _ _ _ _ _ =>
    evalBiv_rel (relDeg lv2.size) Pt (lin2_ℓ _ _ _) (lin2_ℓ _ _ _)
  have hℓ : lv2.ℓ (o2.add (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0))
      (o2.add (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0))
        (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0)))) ≤ deg0 Pt :=
    le_trans (lv2.size.ℓ_add _ _) (max_le (hd ..)
      (le_trans (lv2.size.ℓ_add _ _) (max_le (hd ..) (hd ..))))
  have h := lv0.XY_sem (N := N) _ (xa := lin1 0 (-1)) (xb := lin1 0 0) 0 1
    (le_trans (Nat.add_le_add_right hℓ 1) hN) (lin1_ℓ _ _) (lin1_ℓ _ _) ()
  have e : semL (semL lv0.f) (o2.add (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0))
      (o2.add (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0))
        (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0)))) = S0 Pt := by
    funext z
    obtain ⟨c, d, u⟩ := z
    have := congrFun (lv2.hom.add (a := evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0)) rfl
      (lv2.hom.add (a := evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0))
        (a' := evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0)) rfl rfl)) (c, (d, u))
    refine this.trans ?_
    show lv2.f _ _ + (lv2.f _ _ + lv2.f _ _) = _
    rw [ev_lin2, ev_lin2, ev_lin2]
    simp only [S0]; push_cast; ring_nf
  rw [e] at h
  exact h

theorem i2_real (Pt : List (List Int)) {N : ℕ} (hN : dm (deg0 Pt) (deg0 Pt) + 1 ≤ N) :
    ((i2 (lcmUpTo N : ℤ) Pt : ℤ) : ℝ) = (lcmUpTo N : ℝ) ^ 2 * sqR (S2 Pt) := by
  have hd : ∀ a1 b1 c1 a2 b2 c2 : Int,
      lv2.ℓ (o2.mul (evalBiv o2 Pt (lin2 a1 b1 c1) (lin2 a2 b2 c2))
        (evalBiv o2 Pt (lin2 a1 b1 c1) (lin2 a2 b2 c2))) ≤ dm (deg0 Pt) (deg0 Pt) :=
    fun _ _ _ _ _ _ => (relDeg lv2.size).mul
      (evalBiv_rel (relDeg lv2.size) Pt (lin2_ℓ _ _ _) (lin2_ℓ _ _ _))
      (evalBiv_rel (relDeg lv2.size) Pt (lin2_ℓ _ _ _) (lin2_ℓ _ _ _))
  have hℓ : lv2.ℓ (o2.add (o2.mul (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0))
        (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0)))
      (o2.add (o2.mul (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0))
          (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0)))
        (o2.mul (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0))
          (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0))))) ≤ dm (deg0 Pt) (deg0 Pt) :=
    le_trans (lv2.size.ℓ_add _ _) (max_le (hd ..)
      (le_trans (lv2.size.ℓ_add _ _) (max_le (hd ..) (hd ..))))
  have h := lv0.XY_sem (N := N) _ (xa := lin1 0 (-1)) (xb := lin1 0 0) 0 1
    (le_trans (Nat.add_le_add_right hℓ 1) hN) (lin1_ℓ _ _) (lin1_ℓ _ _) ()
  have hm : ∀ (a b : R2) (z : ℝ × ℝ × Unit), lv2.f (o2.mul a b) z = lv2.f a z * lv2.f b z :=
    fun a b z => congrFun (lv2.hom.mul rfl rfl) z
  have e : semL (semL lv0.f) (o2.add (o2.mul (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0))
        (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0)))
      (o2.add (o2.mul (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0))
          (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0)))
        (o2.mul (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0))
          (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0))))) = S2 Pt := by
    funext z
    obtain ⟨c, d, u⟩ := z
    have := congrFun (lv2.hom.add (a := o2.mul (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0))
        (evalBiv o2 Pt (lin2 1 0 0) (lin2 0 1 0))) rfl
      (lv2.hom.add (a := o2.mul (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0))
          (evalBiv o2 Pt (lin2 (-1) (-1) 0) (lin2 1 0 0)))
        (a' := o2.mul (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0))
          (evalBiv o2 Pt (lin2 0 1 0) (lin2 (-1) (-1) 0))) rfl rfl)) (c, (d, u))
    refine this.trans ?_
    show lv2.f _ _ + (lv2.f _ _ + lv2.f _ _) = _
    rw [hm, hm, hm, ev_lin2, ev_lin2, ev_lin2]
    simp only [S2]; push_cast; ring_nf
  rw [e] at h
  exact h

end XiPrime8845.Triple.IntCheck.Sem

#print axioms XiPrime8845.Triple.IntCheck.Sem.j4_real
#print axioms XiPrime8845.Triple.IntCheck.Sem.j3_real
#print axioms XiPrime8845.Triple.IntCheck.Sem.i0_real
#print axioms XiPrime8845.Triple.IntCheck.Sem.i2_real
