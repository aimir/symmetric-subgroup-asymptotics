import SymmetricSubgroupAsymptotics.SixPointTernaryAxesNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Original row159 is the selected sum/difference-axis image pilot.
The actual six-pair action is contained in the shared image by four literal
original-generator codes. The pullback argument retains its original group
and every original normal quotient. Its historical (2,1) record admits the
proved alternate profile (3,1). -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAxesImagePilot

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue SixPointTernaryAxesNormalGenerators

def row159Codes : Fin 4 → Model :=
  ![1, (translation,translation), (translation,translation ^ 2), (reflection,1)]

def row159Tops (i : Fin 4) : Equiv.Perm (Fin 6) := literalAction (row159Codes i)

theorem row159_preserves : ∀ i,
    BinaryPairFrame.Preserves SixPairCyclicSymmetricSocles.pointChart
      (row159Generators i) (row159Tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def row159Frame : BinaryPairFrame Row159Top (Fin 6) :=
  BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row159Generators row159Tops row159_preserves

theorem row159_range_le : row159Frame.top.range ≤ literalAction.range := by
  change (BinaryPairFrame.ofGenerators SixPairCyclicSymmetricSocles.pointChart
    row159Generators row159Tops row159_preserves).top.range ≤ literalAction.range
  rw [BinaryPairFrame.ofGenerators_top_range]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨row159Codes i,rfl⟩

theorem row159AtThree_quotientSocle (N : Subgroup Row159Top) [N.Normal] :
    SocleNormalGeneratorBound (Row159Top ⧸ N) 3 :=
  quotientSocle_of_original_natural row159Frame row159_range_le
    PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily.row159Natural N

def row159AtThree_family : row159Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact row159AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryAxesImagePilot

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveTernaryAxesImagePilot

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def row159At3 : DegreeTwoTwelveJointFiniteRowData row159Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveTernaryAxesImagePilot.row159AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily.row159Natural

noncomputable def row159At3Data : DegreeTwoTwelveFlexibleProfiles.Data row159Interface :=
  .ofExact row159At3 (by decide +kernel)

end DegreeTwoTwelveTernaryAxesImagePilot
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
