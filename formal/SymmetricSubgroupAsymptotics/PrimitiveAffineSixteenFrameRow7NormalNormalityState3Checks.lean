import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalCore


/-! Normality checks for state 3.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalNormalityState3Checks

abbrev Source := PrimitiveAffineSixteenFrameRow7NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow7TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 6)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 4) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  positiveWordsTable[j.val * 6 + k.val]!

private def negativeWords (j : Fin 4) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  negativeWordsTable[j.val * 6 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 4) (k : Fin 6),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 3 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 3 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 6),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 3 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 3 k)))
          (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3) =
      PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3 k *
        (PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3 k *
      (PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 3 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3) =
      (PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3 k *
        PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3 k *
      PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 3 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 3) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalNormalityState3Checks

end
