import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalCore


/-! Normality checks for state 7.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalNormalityState7Checks

abbrev Source := PrimitiveAffineSixteenFrameRow12NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow12TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 8)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 3) (k : Fin 8) :
    FiniteGeneratorWord (Fin 8) :=
  positiveWordsTable[j.val * 8 + k.val]!

private def negativeWords (j : Fin 3) (k : Fin 8) :
    FiniteGeneratorWord (Fin 8) :=
  negativeWordsTable[j.val * 8 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 3) (k : Fin 8),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 7 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 7 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 3) (k : Fin 8),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 7 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 7 k)))
          (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 3) (k : Fin 8),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7) =
      PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7 k *
        (PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7 k *
      (PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 7 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 3) (k : Fin 8),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7) =
      (PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7 k *
        PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7 k *
      PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 7 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 7) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalNormalityState7Checks

end
