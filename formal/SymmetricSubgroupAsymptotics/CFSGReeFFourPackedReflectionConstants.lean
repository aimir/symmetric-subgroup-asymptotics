import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedOrderedBitMatrices

/-! Two fixed constants for the selected tail predicate. Opposition is
an existing flat checked prefix table. The negative middle square is
a PERMUTATION of the already checked positive-square entries; two flat
single-product checks bind it to Wm*T*Wm. No new tuple or root-word
computation is used. These constants do not classify the tail. -/
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedReflectionConstants
open BinaryPackedMatrix CFSGReeFFourPackedOrderedBitMatrices
open CFSGReeFFourBinaryOrderedMatrixData

private def middleIndex : Fin 26→Fin 26 :=
  ![0,1,2,6,5,4,3,10,9,8,7,11,17,15,19,13,18,12,16,14,20,24,23,22,21,25]

private def oppositionIndex : Fin 26→Fin 26 :=
  ![0,1,25,24,23,22,21,19,18,16,14,20,17,15,10,13,9,12,8,7,11,6,5,4,3,2]

private def leftSquare : Mat := fun i j=>bitMatrix 1 (middleIndex i) j
private def negativeSquare : Mat := fun i j=>bitMatrix 1 (middleIndex i) (middleIndex j)

def packedOne : Rows 26 := fun i=>2^i.val

def packedOpposition : Rows 26 := fun i=>2^(oppositionIndex i).val

def packedReflection : Rows 26 := fun i=>∑j : Fin 26,
  if (packedBits 1 (middleIndex i)).testBit (middleIndex j).val then 2^j.val else 0

private theorem one_entries : ∀i j : Fin 26,bit (packedOne i) j.val=(1 : Mat) i j := by
  decide +kernel

private theorem opposition_entries : ∀i j : Fin 26,
    bit (packedOpposition i) j.val=prefixMatrix 8 i j := by
  decide +kernel

private theorem reflection_entries : ∀i j : Fin 26,
    bit (packedReflection i) j.val=negativeSquare i j := by
  decide +kernel

private theorem left_entries : ∀i j : Fin 26,leftSquare i j=
    (CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*bitMatrix 1) i j := by
  decide +kernel

private theorem right_entries : ∀i j : Fin 26,negativeSquare i j=
    (leftSquare*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix) i j := by
  decide +kernel

theorem decode_packedOne : decode packedOne=(1 : Mat) := by
  ext i j
  exact one_entries i j

theorem decode_packedOpposition : decode packedOpposition=prefixMatrix 8 := by
  ext i j
  exact opposition_entries i j

theorem decode_packedReflection : decode packedReflection=
    CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*bitMatrix 1*
      CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix := by
  have h0 : decode packedReflection=negativeSquare := by
    ext i j
    exact reflection_entries i j
  have h1 : leftSquare=CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*bitMatrix 1 := by
    ext i j
    exact left_entries i j
  have h2 : negativeSquare=leftSquare*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix := by
    ext i j
    exact right_entries i j
  exact h0.trans (h2.trans (congrArg
    (fun M : Mat=>M*CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix) h1))

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedReflectionConstants
