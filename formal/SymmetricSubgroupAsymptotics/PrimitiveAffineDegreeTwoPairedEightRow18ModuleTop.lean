import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineTops

/-! Semantic natural-module adapter for paired-eight row 18.
The source is the literal affine subgroup; no group table is generated. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18ModuleTop

abbrev Source := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.Source
abbrev group : Group Source := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.group
def generators := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.generators
def originalEquiv := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.originalEquiv
def ambient := PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.ambient
theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ :=
  PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.ambient_full

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow18ModuleTop

end
