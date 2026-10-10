import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops

/-!
# Literal producer interface for paired-eight row 2

The bounded selected producer needs public names for the retained generator
tuple, its literal subgroup, and the already installed finite interface.
This module exposes those names without rebuilding any catalogue data.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineDegreeTwoPairedEightRow2ProducerInterface

def generators : Fin 4 → Equiv.Perm (Fin 8) :=
  PrimitiveAffineEightFrameRow1TopCertificate.generators

abbrev Top : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range generators)

/-- The producer target is exactly the second shared paired-eight top. -/
noncomputable def interface : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairedEightSharedTops.top2

end PrimitiveAffineDegreeTwoPairedEightRow2ProducerInterface
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
