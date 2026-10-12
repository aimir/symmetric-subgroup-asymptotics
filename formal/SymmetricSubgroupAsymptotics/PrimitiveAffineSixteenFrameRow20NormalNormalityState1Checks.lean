import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalCore


/-! Normality checks for state 1.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalNormalityState1Checks

abbrev Source := PrimitiveAffineSixteenFrameRow20NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow20TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 5) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  positiveWordsTable[j.val * 7 + k.val]!

private def negativeWords (j : Fin 5) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  negativeWordsTable[j.val * 7 + k.val]!

private theorem positive_code_checked :
    ∀ (j : Fin 5) (k : Fin 7),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 1 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 5) (k : Fin 7),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 1 k)))
          (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 5) (k : Fin 7),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1) =
      PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1 k *
        (PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1 k *
      (PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 1 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 5) (k : Fin 7),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1) =
      (PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1 k *
        PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1 k *
      PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 1 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 1) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalNormalityState1Checks

end
