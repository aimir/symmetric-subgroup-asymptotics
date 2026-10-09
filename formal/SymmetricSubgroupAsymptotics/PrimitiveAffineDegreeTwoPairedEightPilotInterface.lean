import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0NormalCertificate

/-!
# Paired-eight pilot interface from the shared-top certificates

The first `paired8` row has exactly the literal ordered generators already
checked by `PrimitiveAffineEightFrameRow0TopCertificate`.  This file reuses
that executable Cayley-group and normal-join certificate directly.  The
normal states are transported through the checked group equivalence to the
literal permutation top, with duplicate removal performed by the semantic
range constructor.

The old row-0 module registry is sixteen-dimensional and therefore is not
the natural eight-coordinate pair-top module.  For this pilot we install the
canonical complete registry of all invariant subrepresentations of the
actual eight-coordinate permutation representation.  This establishes a
fully concrete `DegreeTwoPairTopFiniteInterface 8` without a new census or
an unproved completeness flag.  The compressed `pair_top_modules` payload
can replace only that registry while leaving downstream original-normal and
relative-label assembly unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightPilot

abbrev Top : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators)

/-- The old shared-top normal certificate, transported to the literal
degree-eight permutation top. -/
noncomputable def normalRegistry : FiniteNormalStateRegistry Top :=
  FiniteNormalStateRegistry.ofWordRegistryEquiv
    PrimitiveAffineEightFrameRow0NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow0NormalCertificate.topAmbient
    PrimitiveAffineEightFrameRow0NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow0NormalCertificate.data
    PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv

/-- Complete concrete pair-top interface for the selected `paired8-1`
pilot. -/
noncomputable def finiteInterface : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalModuleRegistry
    Top normalRegistry

theorem normal_complete (N : Subgroup finiteInterface.top) [N.Normal] :
    ∃ i, finiteInterface.normalRegistry.state i = N :=
  finiteInterface.normal_complete N

theorem module_complete
    (W : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2)
        finiteInterface.top (Fin 8))) :
    ∃ i, finiteInterface.moduleState i = W :=
  finiteInterface.module_complete W

end DegreeTwoPairedEightPilot
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
