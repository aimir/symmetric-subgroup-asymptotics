import SymmetricSubgroupAsymptotics.FullTernaryWreathPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.PureA4FourOriginalPairFrames
import SymmetricSubgroupAsymptotics.Row203OriginalAbelianAxes
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row203FullWreathOriginalJointData
open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairLocalWreathSocles
abbrev points := PureA4FourOriginalPairFrames.points

def codes : Fin 4 → Model :=
  ![1,firstTranslation,C2Wreath.firstFactor (translation^2*reflection),blockSwap]
def tops : Fin 4 → Equiv.Perm (Fin 6) := fun i => literalAction (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row203Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row203Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row203Generators tops preserves
private theorem reflection_word : literalAction firstReflection=tops 1*tops 2 := by
  decide +kernel

theorem image : frame.top.range=literalAction.range := by
  apply (BinaryPairFrame.ofGenerators_top_range points row203Generators tops preserves).trans
  apply generated_range codes
  · exact Subgroup.subset_closure ⟨1,rfl⟩
  · rw [reflection_word]
    exact (Subgroup.closure (Set.range tops)).mul_mem
      (Subgroup.subset_closure ⟨1,rfl⟩)
      (Subgroup.subset_closure ⟨2,rfl⟩)
  · exact Subgroup.subset_closure ⟨3,rfl⟩

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row203Interface :=
  .ofExact (FullTernaryWreathPairFrameOriginalJointData.jointData row203Interface frame image
    Row203OriginalAbelianAxes.cover Row203OriginalAbelianAxes.cover_surjective
    Row203OriginalAbelianAxes.noTernary
    PrimitiveAffineDegreeTwoTwelveRootInheritanceNaturalFamily.row203Natural) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row203FullWreathOriginalJointData
