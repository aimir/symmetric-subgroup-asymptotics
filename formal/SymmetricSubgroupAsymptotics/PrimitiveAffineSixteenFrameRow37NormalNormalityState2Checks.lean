import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalCore


/-! Normality checks for state 2.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState2Checks

abbrev Source := PrimitiveAffineSixteenFrameRow37NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow37TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 3) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  positiveWordsTable[j.val * 7 + k.val]!

private def negativeWords (j : Fin 3) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  negativeWordsTable[j.val * 7 + k.val]!

private theorem positive_code_checked :
    ∀ (j : Fin 3) (k : Fin 7),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.stateUsed 2 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.stateUsed 2 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 3) (k : Fin 7),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.stateUsed 2 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.stateUsed 2 k)))
          (PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 3) (k : Fin 7),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2) =
      PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2 k *
        (PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2 k *
      (PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.stateUsed 2 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 3) (k : Fin 7),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2) =
      (PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2 k *
        PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2 k *
      PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow37NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow37NormalCore.usedCode (PrimitiveAffineSixteenFrameRow37NormalCore.stateUsed 2 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators 2) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState2Checks

end
