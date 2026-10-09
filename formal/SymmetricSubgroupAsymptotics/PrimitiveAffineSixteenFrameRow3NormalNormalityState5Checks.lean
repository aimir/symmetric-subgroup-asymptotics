import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalCore


/-! Normality checks for state 5.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalNormalityState5Checks

abbrev Source := PrimitiveAffineSixteenFrameRow3NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow3TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.stateUsed 5 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.stateUsed 5 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 3) (k : Fin 5),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.stateUsed 5 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.stateUsed 5 k)))
          (PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 3) (k : Fin 5),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5) =
      PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5 k *
        (PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5 k *
      (PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.stateUsed 5 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 3) (k : Fin 5),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5) =
      (PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5 k *
        PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5 k *
      PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow3NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow3NormalCore.usedCode (PrimitiveAffineSixteenFrameRow3NormalCore.stateUsed 5 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow3NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators 5) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalNormalityState5Checks

end
