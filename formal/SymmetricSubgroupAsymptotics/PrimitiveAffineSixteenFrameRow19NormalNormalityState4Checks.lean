import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalCore


/-! Normality checks for state 4.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalNormalityState4Checks

abbrev Source := PrimitiveAffineSixteenFrameRow19NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow19TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 6)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 4) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  positiveWordsTable[j.val * 6 + k.val]!

private def negativeWords (j : Fin 4) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  negativeWordsTable[j.val * 6 + k.val]!

private theorem positive_code_checked :
    ∀ (j : Fin 4) (k : Fin 6),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.stateUsed 4 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.stateUsed 4 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 4) (k : Fin 6),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.stateUsed 4 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.stateUsed 4 k)))
          (PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4) =
      PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4 k *
        (PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4 k *
      (PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.stateUsed 4 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4) =
      (PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4 k *
        PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4 k *
      PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow19NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow19NormalCore.usedCode (PrimitiveAffineSixteenFrameRow19NormalCore.stateUsed 4 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow19NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators 4) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalNormalityState4Checks

end
