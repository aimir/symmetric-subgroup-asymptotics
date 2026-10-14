import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalCore


/-! Normality checks for state 2.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalNormalityState2Checks

abbrev Source := PrimitiveAffineSixteenFrameRow6NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow6TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.stateUsed 2 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.stateUsed 2 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 6),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.stateUsed 2 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.stateUsed 2 k)))
          (PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2) =
      PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2 k *
        (PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2 k *
      (PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.stateUsed 2 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2) =
      (PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2 k *
        PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2 k *
      PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow6NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow6NormalCore.usedCode (PrimitiveAffineSixteenFrameRow6NormalCore.stateUsed 2 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow6NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators 2) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalNormalityState2Checks

end
