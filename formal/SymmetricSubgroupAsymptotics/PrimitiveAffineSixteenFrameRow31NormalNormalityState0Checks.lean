import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalCore


/-! Normality checks for state 0.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState0Checks

abbrev Source := PrimitiveAffineSixteenFrameRow31NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow31TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.stateUsed 0 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 6),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.stateUsed 0 k)))
          (PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0) =
      PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0 k *
        (PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0 k *
      (PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.stateUsed 0 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 6),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0) =
      (PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0 k *
        PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0 k *
      PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow31NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow31NormalCore.usedCode (PrimitiveAffineSixteenFrameRow31NormalCore.stateUsed 0 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators 0) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState0Checks

end
