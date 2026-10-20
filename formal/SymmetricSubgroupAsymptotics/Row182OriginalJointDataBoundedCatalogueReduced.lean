import SymmetricSubgroupAsymptotics.Row182OriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveNormalConsumerFacts
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveSixKernelCyclicExtensionBoundedCatalogueReduced

/-! Isolated actual degree6/12 normal-consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel

namespace BoundedCatalogueReduced

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle_two
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic (Equiv.Perm (Fin 2)) := isCyclic_of_prime_card (p := 2) (by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])
  exact _root_.SymmetricSubgroupAsymptotics.PrimitiveSixKernelCyclicExtension.BoundedCatalogueReduced.quotientSocle_two socle catalogue
    blockFrame.top top_surjective (blockFrame.kernelCoordinate 0) coordinate_zero_injective N

def quotientFamily
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    row182Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row182Interface.normalRegistry (fun N => by
      letI := N.2
      exact _root_.SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel.BoundedCatalogueReduced.quotientSocle_two socle catalogue N.1)

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row182Interface 2 1 where
  topSocle := _root_.SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel.BoundedCatalogueReduced.quotientFamily socle catalogue
  natural := PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row182Natural

def flexibleData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSixTwelveNormalConsumerFacts) :
    DegreeTwoTwelveFlexibleProfiles.Data row182Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (_root_.SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel.BoundedCatalogueReduced.jointData socle catalogue) (by decide +kernel)

end BoundedCatalogueReduced

end SymmetricSubgroupAsymptotics.Row182OriginalBlockKernel

