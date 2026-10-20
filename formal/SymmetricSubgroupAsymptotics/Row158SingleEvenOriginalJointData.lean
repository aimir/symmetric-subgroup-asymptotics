import SymmetricSubgroupAsymptotics.SingleEvenTernaryPairFrameOriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row158SingleEvenOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SingleEvenTernarySixImage (Model action)
open SixPointTernaryAxesNormalGenerators (translation reflection)
abbrev points := PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pointChart

def codes : Fin 3 → Model :=
  ![1,(Multiplicative.ofAdd 1,translation),(1,translation*reflection)]
def tops : Fin 3 → Equiv.Perm (Fin 6) := fun i => action (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row158Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row158Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row158Generators tops preserves
private theorem range_le : frame.top.range≤action.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range points row158Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private theorem pair_uniform : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) frame.top.range (Fin 6)) 1 :=
  PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pair_uniform 1
    row158Generators tops 1 2 preserves (by decide +kernel) (by decide +kernel)

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row158Interface :=
  .ofExact (SingleEvenTernaryPairFrameOriginalJointData.jointData row158Interface frame range_le
    pair_uniform PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.row158Natural) (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row158SingleEvenOriginalJointData
