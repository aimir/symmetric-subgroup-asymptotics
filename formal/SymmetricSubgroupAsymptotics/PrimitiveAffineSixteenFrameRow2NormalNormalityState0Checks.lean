import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalCore


/-! Normality checks for state 0.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityState0Checks

abbrev Source := PrimitiveAffineSixteenFrameRow2NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 4)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 4)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 4)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 3) (k : Fin 4) :
    FiniteGeneratorWord (Fin 4) :=
  positiveWordsTable[j.val * 4 + k.val]!

private def negativeWords (j : Fin 3) (k : Fin 4) :
    FiniteGeneratorWord (Fin 4) :=
  negativeWordsTable[j.val * 4 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 3) (k : Fin 4),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 0 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 3) (k : Fin 4),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 0 k)))
          (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 3) (k : Fin 4),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0) =
      PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0 k *
        (PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0 k *
      (PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 0 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 3) (k : Fin 4),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0) =
      (PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0 k *
        PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0 k *
      PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 0 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 0) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityState0Checks

end
