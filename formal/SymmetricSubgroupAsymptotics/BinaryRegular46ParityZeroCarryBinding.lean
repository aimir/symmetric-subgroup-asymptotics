import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroCarryCoordinates
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroOuterCarriesData

/-! The independent original state/radical charts use exactly the same
annihilator rows as the literal square-carry Data prefix. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroCarryBinding

theorem state_eq_wideState :
    (BinaryRegular46GraphHeadRigidity.stateChart 0).space =
      BinaryRegular46ParityZeroOuterCarries.wideState :=
  BinaryRegular46ParityZeroCarryCoordinates.state_eq_wideState

theorem radical_eq_lowerRadical :
    BinaryRegular46ParityZeroIntrinsicRadical.radical.space =
      BinaryRegular46ParityZeroOuterCarries.lowerRadical :=
  BinaryRegular46ParityZeroCarryCoordinates.radical_eq_lowerRadical

theorem layerChange_eq : BinaryRegular46ParityZeroOuterCarries.layerChange =
    binaryEightCanonicalLayerChange := rfl

end SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroCarryBinding
