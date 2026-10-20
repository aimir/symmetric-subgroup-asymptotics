import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalCore


/-! Normality checks for state 1.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalNormalityState1Checks

abbrev Source := PrimitiveAffineSixteenFrameRow17NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow17TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.stateUsed 1 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 4) (k : Fin 6),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.stateUsed 1 k)))
          (PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1) =
      PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1 k *
        (PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1 k *
      (PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.stateUsed 1 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1) =
      (PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1 k *
        PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1 k *
      PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow17NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow17NormalCore.usedCode (PrimitiveAffineSixteenFrameRow17NormalCore.stateUsed 1 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators 1) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalNormalityState1Checks

end
