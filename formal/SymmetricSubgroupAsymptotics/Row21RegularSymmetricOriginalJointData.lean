import SymmetricSubgroupAsymptotics.RegularSymmetricSixPairSocles
import SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row21RegularSymmetricOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open RegularSymmetricSixPairSocles (action)
abbrev points := PureA4FourOriginalPairFrames.points

def codes : Fin 3 → DihedralGroup 3 := ![1,.r 1,.sr 1]
def tops : Fin 3 → Equiv.Perm (Fin 6) := fun i => action (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row21Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row21Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row21Generators tops preserves
private theorem range_le : frame.top.range≤action.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range points row21Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private def original : Fin 3 → row21Interface.top := closureGenerators row21Generators
private def c : row21Interface.top := original 1
private def b : row21Interface.top := c*original 2
private theorem rotation_val : frame.top c=BinarySixPointSymmetricMatrixBlocks.rotation :=
  (BinaryPairFrame.ofGenerators_top_generator points row21Generators tops preserves 1).trans
    (by decide +kernel)
private theorem reflection_val : frame.top b=BinarySixPointSymmetricMatrixBlocks.reflection := by
  change frame.top (c*original 2)=_
  rw [map_mul,rotation_val]
  have h := BinaryPairFrame.ofGenerators_top_generator points row21Generators tops preserves 2
  calc
    _=BinarySixPointSymmetricMatrixBlocks.rotation*tops 2 :=
      congrArg (fun p : Equiv.Perm (Fin 6) => BinarySixPointSymmetricMatrixBlocks.rotation*p) h
    _=BinarySixPointSymmetricMatrixBlocks.reflection := by decide +kernel

def jointData : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row21Interface 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact RegularSymmetricSixPairSocles.quotientSocle frame c b rotation_val reflection_val range_le N.1)
  natural := DegreeTwoTwelveThreeBlockNaturalFamily.row21Natural

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row21Interface :=
  .ofExact jointData (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row21RegularSymmetricOriginalJointData
