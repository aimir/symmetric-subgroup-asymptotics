import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalCore


/-! Normality checks for state 0.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalNormalityState0Checks

abbrev Source := PrimitiveAffineSixteenFrameRow15NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow15TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.stateUsed 0 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 5),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.stateUsed 0 k)))
          (PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 5),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0) =
      PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0 k *
        (PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0 k *
      (PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.stateUsed 0 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 5),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0) =
      (PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0 k *
        PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0 k *
      PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow15NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow15NormalCore.usedCode (PrimitiveAffineSixteenFrameRow15NormalCore.stateUsed 0 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators 0) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalNormalityState0Checks

end
