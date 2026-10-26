import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedReflectionConstants
import SymmetricSubgroupAsymptotics.CFSGReeFFourOrderedTailMaskCoordinates

/-! ONE prescribed sixteen-mask kernel pilot for the compact tail test.
The selection includes the three diagnostic candidate masks and the
all-ones stress mask, fixed before this check. No full1024 classification
or actual-group inference is made here. The opposed product is written
Q*M (rather than M*Q); for involutions these are conjugate, matching the
actual source relation without changing the mathematical condition. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailSixteenPilot
open BinaryPackedMatrix CFSGReeFFourPackedOrderedBitMatrices
open CFSGReeFFourPackedReflectionConstants CFSGReeFFourOrderedTailMaskCoordinates

def packedChart (c : Fin 1024) : Rows 26 :=
  ([2,3,4,5,6,7,8,9,10,11] : List (Fin 12)).foldl
    (fun M i=>if tailBits c i then BinaryPackedMatrix.mul (packedBits i) M else M)
    packedOne

def packedAdmissible (c : Fin 1024) : Bool :=
  let M:=packedChart c
  let Q:=BinaryPackedMatrix.mul (BinaryPackedMatrix.mul packedOpposition M) packedOpposition
  let P:=BinaryPackedMatrix.mul Q M
  decide (M≠packedOne) &&
    decide (BinaryPackedMatrix.mul M M=packedOne) &&
    decide (BinaryPackedMatrix.mul M packedReflection=BinaryPackedMatrix.mul packedReflection M) &&
    decide (P≠packedOne) &&
    decide (BinaryPackedMatrix.mul (BinaryPackedMatrix.mul P P) P=packedOne)

def selectedMasks : Fin 16→Fin 1024 :=
  ![0,1,2,3,4,8,16,32,63,64,127,255,511,512,864,1023]

theorem selected_trial_summary : ∀i : Fin 16,
    packedAdmissible (selectedMasks i)=decide (i=9∨i=13∨i=14) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailSixteenPilot
