import SymmetricSubgroupAsymptotics.Row200SixPairOriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily

/-! Rows208 and260 share the selected literal six-pair chart of row200.
Their actual generator images and six reference words are checked below;
no quotient bound is transported through an overgroup inclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
abbrev pointChart := Row200SixPairOriginalJointData.pointChart

def row208Tops : Fin 3 → Equiv.Perm (Fin 6) :=
  ![1,Row200SixPairOriginalJointData.tops 1,Row200SixPairOriginalJointData.tops 3]
private theorem row208_preserves : ∀ i, BinaryPairFrame.Preserves
    pointChart (row208Generators i) (row208Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row208Frame : BinaryPairFrame row208Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row208Generators row208Tops row208_preserves

def referenceWords {G : Type} [Group G] (t c : G) : Fin 6 → G :=
  ![1,t⁻¹*c,c*t⁻¹*c,t*c,c*t*c,c]
instance row208_top_pretransitive : MulAction.IsPretransitive row208Frame.top.range (Fin 6) :=
  OriginalSixPairNaturalJointData.top_pretransitive row208Frame
    (referenceWords (closureGenerators row208Generators 1) (closureGenerators row208Generators 2))
    (by decide +kernel)

def row208Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row208Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (OriginalSixPairNaturalJointData.jointData socle catalogue row208Interface row208Frame
      PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily.row208Natural) (by decide +kernel)

private theorem row260_preserves : ∀ i, BinaryPairFrame.Preserves
    pointChart (row260Generators i) (Row200SixPairOriginalJointData.tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row260Frame : BinaryPairFrame row260Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row260Generators
    Row200SixPairOriginalJointData.tops row260_preserves
instance row260_top_pretransitive : MulAction.IsPretransitive row260Frame.top.range (Fin 6) :=
  OriginalSixPairNaturalJointData.top_pretransitive row260Frame
    (referenceWords (closureGenerators row260Generators 1) (closureGenerators row260Generators 3))
    (by decide +kernel)

def row260Data (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row260Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (OriginalSixPairNaturalJointData.jointData socle catalogue row260Interface row260Frame
      PrimitiveAffineDegreeTwoTwelveJoinedHalfCycleNaturalFamily.row260Natural) (by decide +kernel)

end SymmetricSubgroupAsymptotics.JoinedHalfCycleSixPairOriginalJointData
