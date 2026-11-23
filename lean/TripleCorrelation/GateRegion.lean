/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.J4Final
import TripleCorrelation.GateReal
import TripleCorrelation.D20Pack

/-! # The gate as an inequality between integrals over hexagon regions (doubled coordinates)

`gate_region` (degree-independent) and its d = 20 instance `P20_region`.  With
`P̃ = PR Pt`, `hexD = {|X|,|Y|,|X+Y| ≤ 1}`:

* `I0D = ∫_{hexD} P̃`, `I2D = ∫_{hexD} P̃²`,
* `J3D = ∫₀¹ T3 + ∫₁² T3`, `T3 d = ∫_{hexD ∩ (hexD − (d,−d))} P̃(w)·P̃(w + (d,−d))·(d − 2)`,
* `J4D = ∫_{Tri} H4`, `H4 (c,d) = ∫_{hexD ∩ (hexD + (c,d))} P̃(w)·P̃(w − (c,d))·d`,

the statement is `I0D ≠ 0` and `(4·I2D + 6·J3D − 6·J4D)·gd ≤ (gn − 2·gd)·I0D²`.
Still open: Jacobians to the original coordinates and the symmetry reduction to `nu3F`. -/

open MeasureTheory Set

namespace XiPrime8845.Triple.Region
open IntCheck IntCheck.Sem

noncomputable def I0D (Pt : List (List Int)) : ℝ := ∫ z in hexD, PR Pt z.1 z.2
noncomputable def I2D (Pt : List (List Int)) : ℝ := ∫ z in hexD, PR Pt z.1 z.2 * PR Pt z.1 z.2
noncomputable def J3D (Pt : List (List Int)) : ℝ :=
  (∫ d in (0 : ℝ)..1, T3 Pt d) + ∫ d in (1 : ℝ)..2, T3 Pt d
noncomputable def J4D (Pt : List (List Int)) : ℝ := ∫ z in Tri, H4 Pt z

theorem gate_region {D N : ℕ} {P : List (List Int)} {gn gd : Int}
    (hdeg : degOK D N P = true) (hg : IntCheck.gate D N P gn gd = true) :
    I0D (scaleTab D 0 P) ≠ 0 ∧
    (4 * I2D (scaleTab D 0 P) + 6 * J3D (scaleTab D 0 P) - 6 * J4D (scaleTab D 0 P)) * gd
      ≤ ((gn : ℝ) - 2 * gd) * I0D (scaleTab D 0 P) ^ 2 := by
  have h := gate_real hdeg hg
  rw [sqR_S0, sqR_S2, J3R_eq, J4R_eq] at h
  exact h

end XiPrime8845.Triple.Region

namespace XiPrime8845.Triple
open IntCheck IntCheck.Sem Region

theorem P20i_degOK' : degOK 10 26 P20i = true := by decide +kernel

/-- d = 20, `c₂₀ = 77223/1000000`. -/
theorem P20_region :
    I0D (scaleTab 10 0 P20i) ≠ 0 ∧
    (4 * I2D (scaleTab 10 0 P20i) + 6 * J3D (scaleTab 10 0 P20i)
        - 6 * J4D (scaleTab 10 0 P20i)) * 1000000
      ≤ ((77223 : ℝ) - 2 * 1000000) * I0D (scaleTab 10 0 P20i) ^ 2 := by
  have := gate_region P20i_degOK' P20i_gate
  simpa using this

end XiPrime8845.Triple

#print axioms XiPrime8845.Triple.Region.gate_region
#print axioms XiPrime8845.Triple.P20_region
