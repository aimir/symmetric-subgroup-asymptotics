import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailSixteenPilot
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixChart

/-! Decode the compact ten-bit product into the already checked literal
Boolean chart.  This is a symbolic fold argument, with no finite cases
and no faithfulness assumption on the group representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailMatrixSemantics
open BinaryPackedMatrix CFSGReeFFourPackedOrderedBitMatrices
open CFSGReeFFourPackedReflectionConstants CFSGReeFFourPackedTailSixteenPilot
open CFSGReeFFourOrderedTailMaskCoordinates CFSGReeFFourBinaryOrderedMatrixData
open CFSGReeFFourBinaryFirstGlobalEntry CFSGReeFFourBinaryOrderedMatrixChart
open MatrixBinaryAffineFactor CFSGFFourNormSparseWordMatrix
open CFSGReeFFourBinaryOrderedRootWords

private theorem decode_selected_fold {n : ℕ} {ι : Type*} (l : List ι)
    (b : ι→Bool) (A : ι→Rows n) (M : Rows n) :
    decode (l.foldl (fun B i=>if b i then BinaryPackedMatrix.mul (A i) B else B) M)=
      l.foldl (fun B i=>if b i then decode (A i)*B else B) (decode M) := by
  induction l generalizing M with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases h : b i <;> simp [h,decode_mul]

private theorem chart_expand (b : Fin 12→ZMod 2) :
    chartMatrix b=
      affineFactor (b 11) (bitMatrix 11)*
      (affineFactor (b 10) (bitMatrix 10)*
      (affineFactor (b 9) (bitMatrix 9)*
      (affineFactor (b 8) (bitMatrix 8)*
      (affineFactor (b 7) (bitMatrix 7)*
      (affineFactor (b 6) (bitMatrix 6)*
      (affineFactor (b 5) (bitMatrix 5)*
      (affineFactor (b 4) (bitMatrix 4)*
      (affineFactor (b 3) (bitMatrix 3)*
      (affineFactor (b 2) (bitMatrix 2)*
      (affineFactor (b 1) (bitMatrix 1)*
      (affineFactor (b 0) (bitMatrix 0)*1))))))))))) := rfl

private theorem selected_step (b : Bool) (A B : Mat) :
    (if b then A*B else B)=affineFactor (if b then 1 else 0) A*B := by
  cases b <;> simp [affineFactor_zero,affineFactor_one]

theorem decode_packedChart (c : Fin 1024) :
    decode (packedChart c)=chartMatrix (bitValues (tailBits c)) := by
  rw [packedChart,decode_selected_fold,decode_packedOne]
  simp_rw [decode_packedBits]
  simp_rw [selected_step]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [chart_expand]
  have h0 : affineFactor (bitValues (tailBits c) 0) (bitMatrix 0)=1 := by
    change affineFactor (0 : ZMod 2) (bitMatrix 0)=1
    exact affineFactor_zero _
  have h1 : affineFactor (bitValues (tailBits c) 1) (bitMatrix 1)=1 := by
    change affineFactor (0 : ZMod 2) (bitMatrix 1)=1
    exact affineFactor_zero _
  rw [h0,h1,Matrix.one_mul,Matrix.one_mul]
  rfl

theorem packedChart_eq_wordMatrix (c : Fin 1024) :
    decode (packedChart c)=wordMatrix (ZMod 2)
      (orderedLetters (CFSGReeFFourBinaryOrderedBooleanParameters.exponentFunction
        (tailBits c)) 8) := by
  rw [decode_packedChart,encoded_word_matrix]

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailMatrixSemantics
