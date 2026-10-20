import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalCore


/-! Normality checks for state 9.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalNormalityState9Checks

abbrev Source := PrimitiveAffineSixteenFrameRow16NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow16TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 9 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 9 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 6),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 9 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 9 k)))
          (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9) =
      PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9 k *
        (PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9 k *
      (PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 9 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9) =
      (PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9 k *
        PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9 k *
      PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 9 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 9) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalNormalityState9Checks

end
