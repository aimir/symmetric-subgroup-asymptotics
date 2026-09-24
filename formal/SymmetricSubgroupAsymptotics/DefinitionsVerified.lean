import SymmetricSubgroupAsymptotics.GaussianCount
import SymmetricSubgroupAsymptotics.Saddle
import SymmetricSubgroupAsymptotics.Constants

/-! The complete semantic and positivity obligations for the explicit benchmarks. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The benchmark definitions have their stated mathematical meaning, with
no additional mathematical assumptions. This does not assert T1, T2 or T3. -/
theorem definitionChecks : DefinitionChecks where
  subgroup_finite := subgroup_finite
  subspace_finite := subspace_finite
  subspace_formula := binarySubspaceCount_eq_gaussianSum
  exact_positive := exactBenchmark_pos
  exact_zero := exactBenchmark_zero
  exact_one := exactBenchmark_one
  saddle_positive_unique := saddle_positive_unique
  saddle_positive := saddleBenchmark_pos
  euler_multipliable := euler_multipliable
  euler_positive := euler_positive
  theta_even_summable := theta_even_summable
  theta_odd_summable := theta_odd_summable
  residue_positive := residue_positive
  elementary_positive := elementary_positive

end SymmetricSubgroupAsymptotics
