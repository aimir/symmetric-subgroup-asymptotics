import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineTops

/-! Semantic natural-module adapter for paired-eight row 20.
The source is the literal affine subgroup; no group table is generated. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20ModuleTop

abbrev Source := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.Source
abbrev group : Group Source := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.group
def generators := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.generators
def originalEquiv := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.originalEquiv
def ambient := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.ambient
theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.ambient_full

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20ModuleTop

end
