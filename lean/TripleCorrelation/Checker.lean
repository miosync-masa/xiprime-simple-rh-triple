/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
The integration regions are transcribed from the ancillary Julia code of
Gonçalves, de Laat and Leijenhorst, arXiv:2303.01095v2 (ZetaWithPolynomials.tar.xz).
-/
import Mathlib.Data.Rat.Defs

/-! # Exact rational checker for the GdLL triple-correlation bound (computation layer)

Gonçalves–de Laat–Leijenhorst, arXiv:2303.01095v2, Section 5. For a polynomial `P(x,y)` with
rational coefficients this file computes, by exact iterated integration of polynomials with
affine limits, the four numbers

* `I0 = ∫_{H₂} P`, `I2 = ∫_{H₂} P²` (hexagon = three images of the square `[-1/2,0]×[0,1/2]`),
* `J3` = the three-fold integral of the paper for `∫₀¹ ĝ(x,-x)(x-1) dx`,
* `J4` = the four-fold integral for `∫₀¹∫_{-x₂}⁰ ĝ(x₁,x₂) x₂ dx₁ dx₂`,

with the region decompositions transcribed from the authors' Julia file
`ZetaWithPolynomials.jl` (`sqint`, `tripleint`, `quadint`), and `certValue = 2 + (I2+6J3-12J4)/I0²`.

**Scope.** This file is the computation layer only. It does NOT prove that these iterated
integrals equal the analytic quantity `ν₃(g)`, nor that the region decomposition is the
intersection of the two hexagons, nor soundness of `integ` against Mathlib integrals.
Branch-only (`gdll-triple-certificate`); not part of v1.0.0 or its SHA256SUMS. -/

namespace XiPrime8845.Triple

/-- Ring operations passed explicitly, so every level is plain structural recursion on lists. -/
structure Ops (R : Type) where
  zero : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  smul : ℚ → R → R
  ofRat : ℚ → R

def ratOps : Ops ℚ := ⟨0, (· + ·), fun a => -a, (· * ·), (· * ·), id⟩

variable {R : Type}

def padd (o : Ops R) : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => o.add a b :: padd o p q

def pmul (o : Ops R) : List R → List R → List R
  | [], _ => []
  | a :: p, q => padd o (q.map (o.mul a)) (o.zero :: pmul o p q)

/-- Polynomials in one more variable (coefficient list, lowest degree first). -/
def polyOps (o : Ops R) : Ops (List R) :=
  ⟨[], padd o, fun p => p.map o.neg, pmul o, fun c p => p.map (o.smul c), fun c => [o.ofRat c]⟩

def horner (o : Ops R) (p : List R) (a : R) : R :=
  p.foldr (fun c acc => o.add c (o.mul a acc)) o.zero

def antiAux (o : Ops R) : ℕ → List R → List R
  | _, [] => []
  | k, c :: p => o.smul (1 / ((k : ℚ) + 1)) c :: antiAux o (k + 1) p

/-- `∫_a^b p(t) dt` in the outer variable; the limits live in the coefficient ring. -/
def integ (o : Ops R) (p : List R) (a b : R) : R :=
  let q := o.zero :: antiAux o 0 p
  o.add (horner o q b) (o.neg (horner o q a))

/-- `P(X,Y)` for a coefficient table `P` (row `i` = coefficients of `x^i y^j`). -/
def evalBiv (o : Ops R) (P : List (List ℚ)) (X Y : R) : R :=
  P.foldr (fun row acc =>
    o.add (row.foldr (fun c a => o.add (o.ofRat c) (o.mul Y a)) o.zero) (o.mul X acc)) o.zero

abbrev R1 := List ℚ
abbrev R2 := List R1
abbrev R3 := List R2
abbrev R4 := List R3

def o1 : Ops R1 := polyOps ratOps
def o2 : Ops R2 := polyOps o1
def o3 : Ops R3 := polyOps o2
def o4 : Ops R4 := polyOps o3

/-- affine form `c0 + cd·d` in `R1` (variable `d`). -/
def lin1 (cd c0 : ℚ) : R1 := [c0, cd]
/-- affine form `c0 + cc·c + cd·d` in `R2` (outer variable `c`). -/
def lin2 (cc cd c0 : ℚ) : R2 := [lin1 cd c0, [cc]]
/-- affine form `c0 + cy·y + cc·c + cd·d` in `R3` (outer variable `y`). -/
def lin3 (cy cc cd c0 : ℚ) : R3 := [lin2 cc cd c0, [[cy]]]
/-- affine form in `R4` (outer variable `x`). -/
def lin4 (cx cy cc cd c0 : ℚ) : R4 := [lin3 cy cc cd c0, [[[cx]]]]

/-! ## Hexagon integral (`sqint`) : variables `x` (outer of `R2`) and `y`. -/

def sqint (f : R2 → R2 → R2) : ℚ :=
  let x := lin2 1 0 0
  let y := lin2 0 1 0
  let q := o2.add (f x y) (o2.add (f (lin2 (-1) (-1) 0) x) (f y (lin2 (-1) (-1) 0)))
  integ ratOps (integ o1 q (lin1 0 (-1/2)) (lin1 0 0)) 0 (1/2)

def I0 (P : List (List ℚ)) : ℚ := sqint (fun X Y => evalBiv o2 P X Y)
def I2 (P : List (List ℚ)) : ℚ :=
  sqint (fun X Y => o2.mul (evalBiv o2 P X Y) (evalBiv o2 P X Y))

/-! ## Three-fold integral (`tripleint`) : `x` outer of `R3`, then `y`, then `z`. -/

def J3 (P : List (List ℚ)) : ℚ :=
  let x := lin3 1 0 0 0
  let y := lin3 0 1 0 0
  let r := o3.mul (o3.mul (evalBiv o3 P x y) (evalBiv o3 P (lin3 1 0 1 0) (lin3 0 1 (-1) 0)))
    (lin3 0 0 1 (-1))
  let a := integ o1 (integ o2 r (lin2 (-1) 0 (-1/2)) (lin2 0 (-1) (1/2))) (lin1 1 (-1/2)) (lin1 0 0)
  let b := integ o1 (integ o2 r (lin2 0 0 (-1/2)) (lin2 0 (-1) (1/2))) (lin1 0 0) (lin1 1 0)
  let c := integ o1 (integ o2 r (lin2 0 0 (-1/2)) (lin2 (-1) 0 (1/2))) (lin1 1 0) (lin1 0 (1/2))
  let t1 := integ ratOps (o1.add a (o1.add b c)) 0 (1/2)
  let d := integ o1 (integ o2 r (lin2 0 0 (-1/2)) (lin2 0 (-1) (1/2))) (lin1 1 (-1/2)) (lin1 0 (1/2))
  let t2 := integ ratOps d (1/2) 1
  t1 + t2

/-! ## Four-fold integral (`quadint`) : `x` outer of `R4`, then `y`, then `c`, then `d`.
Pieces 1,2 use `(c,d) = (z,w)`; pieces 3,4 use `(c,d) = (w,z)`. -/

/-- integrand `P(x,y)·P(x-z,y-w)·w`; `zc = true` means `z` is the variable `c`. -/
def quadIntegrand (P : List (List ℚ)) (zc : Bool) : R4 :=
  let x := lin4 1 0 0 0 0
  let y := lin4 0 1 0 0 0
  let xz := if zc then lin4 1 0 (-1) 0 0 else lin4 1 0 0 (-1) 0
  let yw := if zc then lin4 0 1 0 (-1) 0 else lin4 0 1 (-1) 0 0
  let w := if zc then lin4 0 0 0 1 0 else lin4 0 0 1 0 0
  o4.mul (o4.mul (evalBiv o4 P x y) (evalBiv o4 P xz yw)) w

/-- inner double integral over `x` then `y`. -/
def xy (r : R4) (xa xb : R3) (ya yb : R2) : R2 := integ o2 (integ o3 r xa xb) ya yb

def J4 (P : List (List ℚ)) : ℚ :=
  let r := quadIntegrand P true
  -- piece 1: x ∈ [-1/2, z+1/2], y ∈ [w-1/2, 1/2], z ∈ [-w, -1/2], w ∈ [1/2, 1]
  let a := xy r (lin3 0 0 0 (-1/2)) (lin3 0 1 0 (1/2)) (lin2 0 1 (-1/2)) (lin2 0 0 (1/2))
  let t1 := integ ratOps (integ o1 a (lin1 (-1) 0) (lin1 0 (-1/2))) (1/2) 1
  -- piece 2: x ∈ [-1/2-y+w+z, 1/2-y], y ∈ [w-1/2, 1/2], z ∈ [1/2-w, 0], w ∈ [1/2, 1]
  let b := xy r (lin3 (-1) 1 1 (-1/2)) (lin3 (-1) 0 0 (1/2)) (lin2 0 1 (-1/2)) (lin2 0 0 (1/2))
  let t2 := integ ratOps (integ o1 b (lin1 (-1) (1/2)) (lin1 0 0)) (1/2) 1
  let s := quadIntegrand P false
  -- piece 3 (c = w, d = z): w ∈ [-2z, 1/2-z], z ∈ [-1/2, 0]
  let c := xy s (lin3 0 0 0 (-1/2)) (lin3 (-1) 0 0 (1/2)) (lin2 1 1 0) (lin2 0 0 (1/2))
  let d := xy s (lin3 (-1) 1 1 (-1/2)) (lin3 (-1) 0 0 (1/2)) (lin2 0 (-1) 0) (lin2 1 1 0)
  let e := xy s (lin3 (-1) 1 1 (-1/2)) (lin3 0 0 1 (1/2)) (lin2 1 0 (-1/2)) (lin2 0 (-1) 0)
  let t3 := integ ratOps
    (integ o1 (o2.add c (o2.add d e)) (lin1 (-2) 0) (lin1 (-1) (1/2))) (-1/2) 0
  -- piece 4 (c = w, d = z): w ∈ [-z, -2z], z ∈ [-1/2, 0]
  let f := xy s (lin3 0 0 0 (-1/2)) (lin3 (-1) 0 0 (1/2)) (lin2 0 (-1) 0) (lin2 0 0 (1/2))
  let g := xy s (lin3 0 0 0 (-1/2)) (lin3 0 0 1 (1/2)) (lin2 1 1 0) (lin2 0 (-1) 0)
  let h := xy s (lin3 (-1) 1 1 (-1/2)) (lin3 0 0 1 (1/2)) (lin2 1 0 (-1/2)) (lin2 1 1 0)
  let t4 := integ ratOps
    (integ o1 (o2.add f (o2.add g h)) (lin1 (-1) 0) (lin1 (-2) 0)) (-1/2) 0
  t1 + t2 + t3 + t4

/-- `2 + (∫P² + 6·J3 − 12·J4)/(∫P)²`. -/
def certValue (P : List (List ℚ)) : ℚ := 2 + (I2 P + 6 * J3 P - 12 * J4 P) / (I0 P) ^ 2

/-! ## Invariance under the generators `r = (x,y) ↦ (-y, x+y)` and `s = (x,y) ↦ (y,x)`
of the symmetry group of the hexagon, as polynomial identities (coefficient lists are compared
after subtracting, so trailing zeros do not matter). -/

def isZero1 (p : R1) : Bool := p.all (· == 0)
def isZero2 (p : R2) : Bool := p.all isZero1

def invariant (P : List (List ℚ)) : Bool :=
  let x := lin2 1 0 0
  let y := lin2 0 1 0
  let p := evalBiv o2 P x y
  isZero2 (o2.add (evalBiv o2 P (lin2 0 (-1) 0) (lin2 1 1 0)) (o2.neg p)) &&
  isZero2 (o2.add (evalBiv o2 P y x) (o2.neg p))

end XiPrime8845.Triple
