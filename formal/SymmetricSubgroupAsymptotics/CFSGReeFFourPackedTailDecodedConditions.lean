import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailMatrixSemantics
import SymmetricSubgroupAsymptotics.BinaryPackedMatrixBoundedRows

/-! Width and one-way decoded conditions for the same selected predicate.
No mask is enumerated here.  The finite classifier can only be used after
actual group relations have supplied these genuine matrix conditions. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailDecodedConditions
open BinaryPackedMatrix BinaryPackedMatrixBoundedRows
open CFSGReeFFourPackedOrderedBitMatrices CFSGReeFFourPackedReflectionConstants
open CFSGReeFFourPackedTailSixteenPilot CFSGReeFFourOrderedTailMaskCoordinates

private theorem one_width : Bounded packedOne := by
  change ∀i : Fin 26,packedOne i<2^26
  decide +kernel
private theorem reflection_width : Bounded packedReflection := by
  change ∀i : Fin 26,packedReflection i<2^26
  decide +kernel

theorem packedChart_bounded (c : Fin 1024) : Bounded (packedChart c) := by
  apply foldl_bounded _ _ _ packedOne one_width
  intro i A hA
  split
  · exact mul_bounded (packedBits i) A hA
  · exact hA

def opposedProduct (c : Fin 1024) : Rows 26 :=
  BinaryPackedMatrix.mul
    (BinaryPackedMatrix.mul (BinaryPackedMatrix.mul packedOpposition (packedChart c))
      packedOpposition) (packedChart c)

theorem packedAdmissible_of_decoded (c : Fin 1024)
    (hn : decode (packedChart c)≠1)
    (hs : decode (packedChart c)*decode (packedChart c)=1)
    (hc : decode (packedChart c)*decode packedReflection=
      decode packedReflection*decode (packedChart c))
    (hpn : decode (opposedProduct c)≠1)
    (hps : decode (opposedProduct c)*decode (opposedProduct c)*
      decode (opposedProduct c)=1) : packedAdmissible c=true := by
  have hM := packedChart_bounded c
  have hP : Bounded (opposedProduct c) := mul_bounded _ _ hM
  have hn' : packedChart c≠packedOne := by
    intro h
    exact hn ((congrArg decode h).trans decode_packedOne)
  have hs' : BinaryPackedMatrix.mul (packedChart c) (packedChart c)=packedOne :=
    decode_injective_of_bounded _ _ (mul_bounded _ _ hM) one_width
      (by rw [decode_mul,decode_packedOne]; exact hs)
  have hc' : BinaryPackedMatrix.mul (packedChart c) packedReflection=
      BinaryPackedMatrix.mul packedReflection (packedChart c) :=
    decode_injective_of_bounded _ _ (mul_bounded _ _ reflection_width)
      (mul_bounded _ _ hM) (by simpa only [decode_mul] using hc)
  have hpn' : opposedProduct c≠packedOne := by
    intro h
    exact hpn ((congrArg decode h).trans decode_packedOne)
  have hps' : BinaryPackedMatrix.mul
      (BinaryPackedMatrix.mul (opposedProduct c) (opposedProduct c))
        (opposedProduct c)=packedOne :=
    decode_injective_of_bounded _ _ (mul_bounded _ _ hP) one_width
      (by simp only [decode_mul,decode_packedOne]; exact hps)
  change (decide (packedChart c≠packedOne) &&
    decide (BinaryPackedMatrix.mul (packedChart c) (packedChart c)=packedOne) &&
    decide (BinaryPackedMatrix.mul (packedChart c) packedReflection=
      BinaryPackedMatrix.mul packedReflection (packedChart c)) &&
    decide (opposedProduct c≠packedOne) &&
    decide (BinaryPackedMatrix.mul (BinaryPackedMatrix.mul (opposedProduct c)
      (opposedProduct c)) (opposedProduct c)=packedOne))=true
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨hn',hs'⟩,hc'⟩,hpn'⟩,hps'⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailDecodedConditions
