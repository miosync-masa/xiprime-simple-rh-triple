/-
Copyright (c) 2026 Masamichi Iizumi (Miosync, Inc.). All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/
import RHTripleIntegration.SimpleProportion
import Main

/-! The two final theorems without the hypothesis.

`Main` is the entry module of the compiled release of L. Alpöge's Lean development of the
Riemann Hypothesis (https://proofsandreasons.io/rh-oleans.html); it provides
`riemannHypothesis : RiemannHypothesis`.  That module and everything it imports are loaded as
compiled objects and are not re-checked when this file is compiled; see
`checks/v1.1-port/stage3/REPORT.md` for what was and was not verified. -/

noncomputable section
open Filter

namespace XiPrime8845.RHTripleIntegration

/-- The lower limiting share of ξ′ zeros which are simple and on the critical line is at
least `1 - c20 / 3`, `c20 = 77223/1000000`. -/
theorem xiPrime_simple_proportion_c20_unconditional :
    1-c20/3 ≤ liminf (fun T => (Zeta23.XiPrime.N0simple 0 T : ℝ) /
      (Zeta23.XiPrime.Ncount 0 T : ℝ)) atTop :=
  xiPrime_simple_proportion_c20 riemannHypothesis

/-- At least 97.42 percent. -/
theorem xiPrime_simple_proportion_ge_9742_unconditional :
    (0.9742 : ℝ) ≤ liminf (fun T => (Zeta23.XiPrime.N0simple 0 T : ℝ) /
      (Zeta23.XiPrime.Ncount 0 T : ℝ)) atTop :=
  xiPrime_simple_proportion_ge_9742 riemannHypothesis

end XiPrime8845.RHTripleIntegration

#check XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_c20_unconditional
#check XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_ge_9742_unconditional
#print axioms XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_c20_unconditional
#print axioms XiPrime8845.RHTripleIntegration.xiPrime_simple_proportion_ge_9742_unconditional
