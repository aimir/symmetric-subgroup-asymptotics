import SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily

/-! The already displayed physical frames and reference-point words of rows
198 and 241 feed the shared all-transitive-six original-action theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTernaryPairNaturalOneOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily

private theorem row198_preserves : ∀ i, BinaryPairFrame.Preserves
    PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pointChart
    (row198Generators i) (row198Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row198Frame : BinaryPairFrame row198Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators
    PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pointChart
    row198Generators row198Tops row198_preserves

instance row198_top_pretransitive : MulAction.IsPretransitive row198Frame.top.range (Fin 6) :=
  OriginalSixPairNaturalJointData.top_pretransitive row198Frame
    (transportWord 0 (closureGenerators row198Generators 1) (closureGenerators row198Generators 3))
    (by decide +kernel)

def row198Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row198Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (OriginalSixPairNaturalJointData.jointData socle catalogue row198Interface row198Frame
      row198Natural) (by decide +kernel)

private theorem row241_preserves : ∀ i, BinaryPairFrame.Preserves
    PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.pointChart
    (row241Generators i) (PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.row241Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row241Frame : BinaryPairFrame row241Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators
    PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.pointChart
    row241Generators PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.row241Tops row241_preserves

instance row241_top_pretransitive : MulAction.IsPretransitive row241Frame.top.range (Fin 6) :=
  OriginalSixPairNaturalJointData.top_pretransitive row241Frame
    (transportWord 0 (closureGenerators row241Generators 1) (closureGenerators row241Generators 3))
    (by decide +kernel)

def row241Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row241Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (OriginalSixPairNaturalJointData.jointData socle catalogue row241Interface row241Frame
      PrimitiveAffineDegreeTwoTwelveFullKernelCyclicPairNaturalFamily.row241Natural) (by decide +kernel)

end SymmetricSubgroupAsymptotics.TwoTernaryPairNaturalOneOriginalJointData
