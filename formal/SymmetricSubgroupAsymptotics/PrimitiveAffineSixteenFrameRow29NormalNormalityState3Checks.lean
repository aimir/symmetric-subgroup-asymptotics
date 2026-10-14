import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalCore


/-! Normality checks for state 3.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalNormalityState3Checks

abbrev Source := PrimitiveAffineSixteenFrameRow29NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow29TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 11)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 11)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 11)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 4) (k : Fin 11) :
    FiniteGeneratorWord (Fin 11) :=
  positiveWordsTable[j.val * 11 + k.val]!

private def negativeWords (j : Fin 4) (k : Fin 11) :
    FiniteGeneratorWord (Fin 11) :=
  negativeWordsTable[j.val * 11 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 4) (k : Fin 11),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.stateUsed 3 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.stateUsed 3 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 11),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.stateUsed 3 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.stateUsed 3 k)))
          (PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 11),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3) =
      PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3 k *
        (PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3 k *
      (PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.stateUsed 3 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 11),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3) =
      (PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3 k *
        PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3 k *
      PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow29NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow29NormalCore.usedCode (PrimitiveAffineSixteenFrameRow29NormalCore.stateUsed 3 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators 3) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalNormalityState3Checks

end
