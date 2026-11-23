/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
The integration regions are transcribed from the ancillary Julia code of
Gonçalves, de Laat and Leijenhorst, arXiv:2303.01095v2 (ZetaWithPolynomials.tar.xz).
-/
import TripleCorrelation.Checker

/-! # Integer-only version of the checker (for kernel evaluation)

Same iterated integrals as `Checker.lean`, in the doubled coordinates `X = 2x` (all limits
become integer affine forms) and with every antiderivative multiplied by a fixed integer
`L` (so `1/(k+1)` becomes the exact integer `L/(k+1)`; `antiOK` checks the divisibility).
No division, no gcd: only `Int` addition and multiplication.

With `D` = degree bound used for clearing powers of two and `Pt(X,Y) = 2^D·P(X/2,Y/2)`:
`i0 = L²·∫Pt`, `i2 = L²·∫Pt²`, `j3 = L³·∫Pt·Pt(X+Z,Y−Z)(Z−2)`, `j4 = L⁴·∫Pt·Pt(X−Z,Y−W)·W`, and
`certValue P = 2 + (4·i2·L² + 6·j3·L − 6·j4)/i0²` (hand computation of the Jacobians; it is
cross-checked against `Checker.certValue` by `#eval` in the data files, not yet proved). -/

namespace XiPrime8845.Triple.IntCheck

structure Ops (R : Type) where
  zero : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  smul : Int → R → R
  ofInt : Int → R

def intOps : Ops Int := ⟨0, (· + ·), fun a => -a, (· * ·), (· * ·), id⟩

variable {R : Type}

def padd (o : Ops R) : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => o.add a b :: padd o p q

def pmul (o : Ops R) : List R → List R → List R
  | [], _ => []
  | a :: p, q => padd o (q.map (o.mul a)) (o.zero :: pmul o p q)

def polyOps (o : Ops R) : Ops (List R) :=
  ⟨[], padd o, fun p => p.map o.neg, pmul o, fun c p => p.map (o.smul c), fun c => [o.ofInt c]⟩

def horner (o : Ops R) (p : List R) (a : R) : R :=
  p.foldr (fun c acc => o.add c (o.mul a acc)) o.zero

def antiAux (o : Ops R) (L : Int) : ℕ → List R → List R
  | _, [] => []
  | k, c :: p => o.smul (L / ((k : Int) + 1)) c :: antiAux o L (k + 1) p

/-- `L·∫_a^b p(t) dt`. Exact when `k+1 ∣ L` for every `k < p.length`. -/
def integ (o : Ops R) (L : Int) (p : List R) (a b : R) : R :=
  let q := o.zero :: antiAux o L 0 p
  o.add (horner o q b) (o.neg (horner o q a))

def evalBiv (o : Ops R) (P : List (List Int)) (X Y : R) : R :=
  P.foldr (fun row acc =>
    o.add (row.foldr (fun c a => o.add (o.ofInt c) (o.mul Y a)) o.zero) (o.mul X acc)) o.zero

abbrev R1 := List Int
abbrev R2 := List R1
abbrev R3 := List R2
abbrev R4 := List R3

def o1 : Ops R1 := polyOps intOps
def o2 : Ops R2 := polyOps o1
def o3 : Ops R3 := polyOps o2
def o4 : Ops R4 := polyOps o3

def lin1 (cd c0 : Int) : R1 := [c0, cd]
def lin2 (cc cd c0 : Int) : R2 := [lin1 cd c0, [cc]]
def lin3 (cy cc cd c0 : Int) : R3 := [lin2 cc cd c0, [[cy]]]
def lin4 (cx cy cc cd c0 : Int) : R4 := [lin3 cy cc cd c0, [[[cx]]]]

/-- `Pt(X,Y) = 2^D · P(X/2, Y/2)` as an integer table (`D ≥` total degree). -/
def scaleRow (D i : ℕ) : ℕ → List Int → List Int
  | _, [] => []
  | j, c :: r => c * 2 ^ (D - i - j) :: scaleRow D i (j + 1) r

def scaleTab (D : ℕ) : ℕ → List (List Int) → List (List Int)
  | _, [] => []
  | i, row :: t => scaleRow D i 0 row :: scaleTab D (i + 1) t

def sqint (L : Int) (f : R2 → R2 → R2) : Int :=
  let x := lin2 1 0 0
  let y := lin2 0 1 0
  let q := o2.add (f x y) (o2.add (f (lin2 (-1) (-1) 0) x) (f y (lin2 (-1) (-1) 0)))
  integ intOps L (integ o1 L q (lin1 0 (-1)) (lin1 0 0)) 0 1

def i0 (L : Int) (Pt : List (List Int)) : Int := sqint L (fun X Y => evalBiv o2 Pt X Y)
def i2 (L : Int) (Pt : List (List Int)) : Int :=
  sqint L (fun X Y => o2.mul (evalBiv o2 Pt X Y) (evalBiv o2 Pt X Y))

def j3 (L : Int) (Pt : List (List Int)) : Int :=
  let x := lin3 1 0 0 0
  let y := lin3 0 1 0 0
  let r := o3.mul (o3.mul (evalBiv o3 Pt x y) (evalBiv o3 Pt (lin3 1 0 1 0) (lin3 0 1 (-1) 0)))
    (lin3 0 0 1 (-2))
  let a := integ o1 L (integ o2 L r (lin2 (-1) 0 (-1)) (lin2 0 (-1) 1)) (lin1 1 (-1)) (lin1 0 0)
  let b := integ o1 L (integ o2 L r (lin2 0 0 (-1)) (lin2 0 (-1) 1)) (lin1 0 0) (lin1 1 0)
  let c := integ o1 L (integ o2 L r (lin2 0 0 (-1)) (lin2 (-1) 0 1)) (lin1 1 0) (lin1 0 1)
  let t1 := integ intOps L (o1.add a (o1.add b c)) 0 1
  let d := integ o1 L (integ o2 L r (lin2 0 0 (-1)) (lin2 0 (-1) 1)) (lin1 1 (-1)) (lin1 0 1)
  let t2 := integ intOps L d 1 2
  t1 + t2

def quadIntegrand (Pt : List (List Int)) (zc : Bool) : R4 :=
  let x := lin4 1 0 0 0 0
  let y := lin4 0 1 0 0 0
  let xz := if zc then lin4 1 0 (-1) 0 0 else lin4 1 0 0 (-1) 0
  let yw := if zc then lin4 0 1 0 (-1) 0 else lin4 0 1 (-1) 0 0
  let w := if zc then lin4 0 0 0 1 0 else lin4 0 0 1 0 0
  o4.mul (o4.mul (evalBiv o4 Pt x y) (evalBiv o4 Pt xz yw)) w

def xy (L : Int) (r : R4) (xa xb : R3) (ya yb : R2) : R2 :=
  integ o2 L (integ o3 L r xa xb) ya yb

def j4 (L : Int) (Pt : List (List Int)) : Int :=
  let r := quadIntegrand Pt true
  let a := xy L r (lin3 0 0 0 (-1)) (lin3 0 1 0 1) (lin2 0 1 (-1)) (lin2 0 0 1)
  let t1 := integ intOps L (integ o1 L a (lin1 (-1) 0) (lin1 0 (-1))) 1 2
  let b := xy L r (lin3 (-1) 1 1 (-1)) (lin3 (-1) 0 0 1) (lin2 0 1 (-1)) (lin2 0 0 1)
  let t2 := integ intOps L (integ o1 L b (lin1 (-1) 1) (lin1 0 0)) 1 2
  let s := quadIntegrand Pt false
  let c := xy L s (lin3 0 0 0 (-1)) (lin3 (-1) 0 0 1) (lin2 1 1 0) (lin2 0 0 1)
  let d := xy L s (lin3 (-1) 1 1 (-1)) (lin3 (-1) 0 0 1) (lin2 0 (-1) 0) (lin2 1 1 0)
  let e := xy L s (lin3 (-1) 1 1 (-1)) (lin3 0 0 1 1) (lin2 1 0 (-1)) (lin2 0 (-1) 0)
  let t3 := integ intOps L
    (integ o1 L (o2.add c (o2.add d e)) (lin1 (-2) 0) (lin1 (-1) 1)) (-1) 0
  let f := xy L s (lin3 0 0 0 (-1)) (lin3 (-1) 0 0 1) (lin2 0 (-1) 0) (lin2 0 0 1)
  let g := xy L s (lin3 0 0 0 (-1)) (lin3 0 0 1 1) (lin2 1 1 0) (lin2 0 (-1) 0)
  let h := xy L s (lin3 (-1) 1 1 (-1)) (lin3 0 0 1 1) (lin2 1 0 (-1)) (lin2 1 1 0)
  let t4 := integ intOps L
    (integ o1 L (o2.add f (o2.add g h)) (lin1 (-1) 0) (lin1 (-2) 0)) (-1) 0
  t1 + t2 + t3 + t4

/-- `lcm(1..n)`. -/
def lcmUpTo : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmUpTo n) (n + 1)

/-- numerator and denominator of `certValue − 2` : `(4·i2·L² + 6·j3·L − 6·j4, i0²)`. -/
def numDen (D N : ℕ) (P : List (List Int)) : Int × Int :=
  let L : Int := lcmUpTo N
  let Pt := scaleTab D 0 P
  (4 * i2 L Pt * L ^ 2 + 6 * j3 L Pt * L - 6 * j4 L Pt, i0 L Pt ^ 2)

/-- the gate `certValue ≤ gn/gd`, cross-multiplied (`gd > 0`, `i0 ≠ 0`). -/
def gate (D N : ℕ) (P : List (List Int)) (gn gd : Int) : Bool :=
  match numDen D N P with
  | (n, d) => decide (0 < d) && decide (n * gd ≤ (gn - 2 * gd) * d)

end XiPrime8845.Triple.IntCheck
