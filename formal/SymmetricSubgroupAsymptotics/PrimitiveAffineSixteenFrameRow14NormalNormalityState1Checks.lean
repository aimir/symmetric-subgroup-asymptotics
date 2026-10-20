import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalCore


/-! Normality checks for state 1.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState1Checks

abbrev Source := PrimitiveAffineSixteenFrameRow14NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow14TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 5)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 4) (k : Fin 5) :
    FiniteGeneratorWord (Fin 5) :=
  positiveWordsTable[j.val * 5 + k.val]!

private def negativeWords (j : Fin 4) (k : Fin 5) :
    FiniteGeneratorWord (Fin 5) :=
  negativeWordsTable[j.val * 5 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 4) (k : Fin 5),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.stateUsed 1 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 5),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.stateUsed 1 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.stateUsed 1 k)))
          (PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 5),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1) =
      PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1 k *
        (PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1 k *
      (PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.stateUsed 1 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 5),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1) =
      (PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1 k *
        PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1 k *
      PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow14NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow14NormalCore.usedCode (PrimitiveAffineSixteenFrameRow14NormalCore.stateUsed 1 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators 1) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState1Checks

end
