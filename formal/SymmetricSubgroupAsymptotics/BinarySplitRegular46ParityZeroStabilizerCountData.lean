import SymmetricSubgroupAsymptotics.BinarySplitRegular46FullConstantStabilizerData
import SymmetricSubgroupAsymptotics.BinaryRegular46ParityZeroCarryCoordinates

/-! The parity-zero count pilot reuses the already checked SAME128
original regular-K46 affine rows. Only its smaller original state and
radical and its quotient section differ from the full-constant case. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinarySplitRegular46ParityZeroStabilizer
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
abbrev state := BinaryRegular46GraphHeadRigidity.stateChart 0
abbrev radical := BinaryRegular46ParityZeroIntrinsicRadical.radical
abbrev topPermutation := BinarySplitRegular46FullConstantStabilizer.topPermutation
abbrev destinationOffset := BinarySplitRegular46FullConstantStabilizer.destinationOffset
abbrev rowAction := BinarySplitRegular46FullConstantStabilizer.rowAction

def projection : V →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v i := binaryRowFunctional
    (binaryVectorOfMask 16 (BinaryRegular46ParityZeroCarryCoordinates.stateAnnihilator i)) v
  map_add' v z := by funext i;exact map_add (binaryRowFunctional _) v z
  map_smul' c v := by funext i;exact map_smul (binaryRowFunctional _) c v

def sectionMap : (Fin 8 → ZMod 2) →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 16 8
    (![1,256,512,1024,2048,4096,8192,16384] : Fin 8 → ℕ)).mulVecLin

theorem quotient_basis : ∀ j : Fin 16,
    Pi.single j 1 - sectionMap (projection (Pi.single j 1)) ∈ state.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

end SymmetricSubgroupAsymptotics.BinarySplitRegular46ParityZeroStabilizer
