import RHTripleIntegration.SimpleProportion
open XiPrime8845

-- 4. the two sets of definitions are definitionally equal
example : @RHTriple.nu3F = @Triple.Nu3.nu3F := rfl
example : @RHTriple.nu3Mass = @Triple.Nu3.mass := rfl
example : @RHTriple.nu3Kernel = @Triple.Nu3.K := rfl
example : @RHTriple.lineInt = @Triple.Nu3.lineInt := rfl
example : @RHTriple.CertificateSmoothing.hexGauge = @Triple.Nu3.hexSum := rfl

-- 2, 3. the final theorems
set_option pp.fullNames true in
#check @RHTripleIntegration.xiPrime_simple_proportion_c20
set_option pp.fullNames true in
#check @RHTripleIntegration.xiPrime_simple_proportion_ge_9742
#print axioms RHTripleIntegration.xiPrime_simple_proportion_c20
#print axioms RHTripleIntegration.xiPrime_simple_proportion_ge_9742
#print RHTripleIntegration.c20
#print RiemannHypothesis
example : (1 : ℝ) - RHTripleIntegration.c20 / 3 = 974259 / 1000000 := by
  norm_num [RHTripleIntegration.c20]
example : (0.9742 : ℝ) ≤ 974259 / 1000000 ∧ (974259 / 1000000 : ℝ) < 0.9743 := by norm_num
