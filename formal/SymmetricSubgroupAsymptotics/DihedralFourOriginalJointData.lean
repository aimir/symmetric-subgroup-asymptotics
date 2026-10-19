import SymmetricSubgroupAsymptotics.DihedralFourOriginalFrames
import SymmetricSubgroupAsymptotics.DihedralPairFrameCyclicAxesJointData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlipNormNaturalFamily

/-! Four literal original actions consume one dihedral pair-frame theorem,
using checked original natural-two bounds and exact original abelian axes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralFourOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open DihedralFourOriginalFrames
open DihedralFourOriginalAbelianAxes

def row108Data : DegreeTwoTwelveFlexibleProfiles.Data row108Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (DihedralPairFrameCyclicAxesJointData.jointData row108Interface
      (frame 0) (cycleElement 0) (top_cycle 0) (top_image 0)
      (a 0) (b 0) (original 0) (closureGenerators_full (generators 0))
      (generator_axes 0) DegreeTwoTwelveSharedNaturalWitnesses.row108Natural) (by decide +kernel)

def row109Data : DegreeTwoTwelveFlexibleProfiles.Data row109Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (DihedralPairFrameCyclicAxesJointData.jointData row109Interface
      (frame 1) (cycleElement 1) (top_cycle 1) (top_image 1)
      (a 1) (b 1) (original 1) (closureGenerators_full (generators 1))
      (generator_axes 1) DegreeTwoTwelveSharedNaturalWitnesses.row109Natural) (by decide +kernel)

def row154Data : DegreeTwoTwelveFlexibleProfiles.Data row154Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (DihedralPairFrameCyclicAxesJointData.jointData row154Interface
      (frame 2) (cycleElement 2) (top_cycle 2) (top_image 2)
      (a 2) (b 2) (original 2) (closureGenerators_full (generators 2))
      (generator_axes 2) PrimitiveAffineDegreeTwoTwelveFlipNormNaturalFamily.row154NaturalTwo) (by decide +kernel)

def row155Data : DegreeTwoTwelveFlexibleProfiles.Data row155Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (DihedralPairFrameCyclicAxesJointData.jointData row155Interface
      (frame 3) (cycleElement 3) (top_cycle 3) (top_image 3)
      (a 3) (b 3) (original 3) (closureGenerators_full (generators 3))
      (generator_axes 3) PrimitiveAffineDegreeTwoTwelveFlipNormNaturalFamily.row155NaturalTwo) (by decide +kernel)

end SymmetricSubgroupAsymptotics.DihedralFourOriginalJointData
