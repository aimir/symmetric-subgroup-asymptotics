import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalCore


/-! Normality checks for state 2.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalNormalityState2Checks

abbrev Source := PrimitiveAffineSixteenFrameRow8NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow8TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 6)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 3) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  positiveWordsTable[j.val * 6 + k.val]!

private def negativeWords (j : Fin 3) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  negativeWordsTable[j.val * 6 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 3) (k : Fin 6),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 2 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 2 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 3) (k : Fin 6),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 2 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 2 k)))
          (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 3) (k : Fin 6),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2) =
      PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2 k *
        (PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2 k *
      (PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 2 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 3) (k : Fin 6),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2) =
      (PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2 k *
        PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2 k *
      PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 2 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 2) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalNormalityState2Checks

end
