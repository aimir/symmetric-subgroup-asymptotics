import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalCore


/-! Normality checks for state 1.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState1Checks

abbrev Source := PrimitiveAffineSixteenFrameRow5NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 5)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 3) (k : Fin 5) :
    FiniteGeneratorWord (Fin 5) :=
  positiveWordsTable[j.val * 5 + k.val]!

private def negativeWords (j : Fin 3) (k : Fin 5) :
    FiniteGeneratorWord (Fin 5) :=
  negativeWordsTable[j.val * 5 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 3) (k : Fin 5),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 1 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 3) (k : Fin 5),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 1 k)))
          (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 3) (k : Fin 5),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1) =
      PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1 k *
        (PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1 k *
      (PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 1 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 3) (k : Fin 5),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1) =
      (PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1 k *
        PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1 k *
      PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 1 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 1) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState1Checks

end
