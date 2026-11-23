/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import TripleCorrelation.P20
import TripleCorrelation.PackSound

/-! d = 20 trial (9 basis polynomials, degree ≤ 10), kernel evaluation only.
Table value 0.077222625 (above the 0.0772 gate; this is the trial run). -/
namespace XiPrime8845.Triple
open IntCheck

theorem P20i_bound : Pack.boundCheck ⟨330, 25⟩ 10 26 P20i = true := by decide +kernel
theorem P20i_gate_pack : Pack.gate ⟨330, 25⟩ 10 26 P20i 77223 1000000 = true := by
  decide +kernel
theorem P20i_gate : IntCheck.gate 10 26 P20i 77223 1000000 = true :=
  (Pack.gate_eq P20i_bound _ _).symm.trans P20i_gate_pack
end XiPrime8845.Triple
#print axioms XiPrime8845.Triple.P20i_gate
