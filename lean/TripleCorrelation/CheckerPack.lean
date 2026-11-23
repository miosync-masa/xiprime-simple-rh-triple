/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.Generic

/-! # Packed version of the integer checker (kernel-friendly)

Same integrals as `CheckerInt.lean`.  The two outer variables `x, y` stay coefficient lists
(`Gen.G3`, `Gen.G4` at `K = Int`); the two inner variables `c, d` are packed into one integer
by Kronecker substitution `d ↦ 2^b`, `c ↦ 2^(b·n)`, so that the bulk of the arithmetic is
big-integer arithmetic.  The two inner integrations read the coefficients back (`unpack`,
balanced digits).

Reading back is lossless only when all coefficients are below `2^(b-1)` in absolute value and
all inner degrees are below `n`.  `boundCheck` verifies a sufficient condition by running the
same generic code on a size bound `(norm, degree)`; `PackSound.lean` proves
`boundCheck = true → Pack.numDen = IntCheck.numDen`. -/

namespace XiPrime8845.Triple.IntCheck.Pack

structure Cfg where
  b : ℕ
  n : ℕ

/-- `2^m` computed in `ℕ` (so the kernel uses its big-number primitive). -/
def pw (m : ℕ) : Int := ((2 ^ m : ℕ) : Int)

def lk3 (g : Cfg) (cd c0 : Int) : Int := cd * pw g.b + c0
def lk4 (g : Cfg) (cc cd c0 : Int) : Int := cc * pw (g.b * g.n) + cd * pw g.b + c0

/-- `h·(1 + R + … + R^(n-1))`: the offset that makes all balanced digits nonnegative. -/
def hsum (R h : Int) : ℕ → Int
  | 0 => 0
  | n + 1 => h + R * hsum R h n

/-- the `n` lowest balanced digits of `u - hsum` in radix `R = 2h`. -/
def unpack (R h : Int) : ℕ → Int → List Int
  | 0, _ => []
  | n + 1, u => (u % R - h) :: unpack R h n (u / R)

/-- `L·∫_a^b` of the polynomial whose packed value in radix `2^e` (`n` digits) is `v`. -/
def integPacked (e n : ℕ) (L v a b : Int) : Int :=
  integ intOps L (unpack (pw e) (pw (e - 1)) n (v + hsum (pw e) (pw (e - 1)) n)) a b

/-- integrate `c` (limits packed in `d`) and then `d` (integer limits). -/
def cdInt (g : Cfg) (L v ca cb da db : Int) : Int :=
  integPacked g.b g.n L (integPacked (g.b * g.n) g.n L v ca cb) da db

def j3 (g : Cfg) (L : Int) (Pt : List (List Int)) : Int :=
  integPacked g.b g.n L (Gen.G3 intOps (lk3 g) L Pt).1 0 1
    + integPacked g.b g.n L (Gen.G3 intOps (lk3 g) L Pt).2 1 2

def j4 (g : Cfg) (L : Int) (Pt : List (List Int)) : Int :=
  cdInt g L (Gen.G4 intOps (lk4 g) L Pt).1 (lk3 g (-1) 0) (lk3 g 0 (-1)) 1 2
    + cdInt g L (Gen.G4 intOps (lk4 g) L Pt).2.1 (lk3 g (-1) 1) (lk3 g 0 0) 1 2
    + cdInt g L (Gen.G4 intOps (lk4 g) L Pt).2.2.1 (lk3 g (-2) 0) (lk3 g (-1) 1) (-1) 0
    + cdInt g L (Gen.G4 intOps (lk4 g) L Pt).2.2.2 (lk3 g (-1) 0) (lk3 g (-2) 0) (-1) 0

def numDen (g : Cfg) (D N : ℕ) (P : List (List Int)) : Int × Int :=
  (4 * i2 (lcmUpTo N) (scaleTab D 0 P) * (lcmUpTo N : Int) ^ 2
      + 6 * j3 g (lcmUpTo N) (scaleTab D 0 P) * (lcmUpTo N : Int)
      - 6 * j4 g (lcmUpTo N) (scaleTab D 0 P),
    i0 (lcmUpTo N) (scaleTab D 0 P) ^ 2)

def gate (g : Cfg) (D N : ℕ) (P : List (List Int)) (gn gd : Int) : Bool :=
  match numDen g D N P with
  | (n, d) => decide (0 < d) && decide (n * gd ≤ (gn - 2 * gd) * d)

/-! ## Size bound (norm, degree+1) -/

/-- degree-like product: `0` is "zero polynomial", `k+1` is "degree ≤ k". -/
def dm (x y : ℕ) : ℕ := if x = 0 ∨ y = 0 then 0 else x + y - 1

def oAbs : Ops (ℕ × ℕ) :=
  ⟨(0, 0), fun a b => (a.1 + b.1, max a.2 b.2), id, fun a b => (a.1 * b.1, dm a.2 b.2),
    fun c a => (c.natAbs * a.1, a.2), fun c => (c.natAbs, 1)⟩

def absK1 (cd c0 : Int) : ℕ × ℕ := (c0.natAbs + cd.natAbs, 2)
def absK2 (cc cd c0 : Int) : ℕ × ℕ := (c0.natAbs + cd.natAbs + 2 * cc.natAbs, 2)

/-- sufficient for reading back the `d`-digits of a polynomial of size `s`. -/
def okD (g : Cfg) (s : ℕ × ℕ) : Bool := decide (2 * s.1 < 2 ^ g.b) && decide (s.2 ≤ g.n)

/-- sufficient for reading back first the `c`-digits and then, after the `c`-integration
(limits of norm ≤ 2, degree ≤ 1), the `d`-digits. -/
def okCD (g : Cfg) (L : Int) (s : ℕ × ℕ) : Bool :=
  decide (2 * (2 * (2 * (L.natAbs * s.1))) < 2 ^ g.b) && decide (2 * s.1 < 2 ^ g.b)
    && decide (s.2 + 1 ≤ g.n)

def boundCheck (g : Cfg) (D N : ℕ) (P : List (List Int)) : Bool :=
  decide (0 < g.b) && decide (0 < g.n)
    && okD g (Gen.G3 oAbs absK1 (lcmUpTo N) (scaleTab D 0 P)).1
    && okD g (Gen.G3 oAbs absK1 (lcmUpTo N) (scaleTab D 0 P)).2
    && okCD g (lcmUpTo N) (Gen.G4 oAbs absK2 (lcmUpTo N) (scaleTab D 0 P)).1
    && okCD g (lcmUpTo N) (Gen.G4 oAbs absK2 (lcmUpTo N) (scaleTab D 0 P)).2.1
    && okCD g (lcmUpTo N) (Gen.G4 oAbs absK2 (lcmUpTo N) (scaleTab D 0 P)).2.2.1
    && okCD g (lcmUpTo N) (Gen.G4 oAbs absK2 (lcmUpTo N) (scaleTab D 0 P)).2.2.2

end XiPrime8845.Triple.IntCheck.Pack
