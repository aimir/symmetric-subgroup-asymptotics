import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalCore


/-! Normality checks for state 0.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalNormalityState0Checks

abbrev Source := PrimitiveAffineSixteenFrameRow26NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow26TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 8)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 4) (k : Fin 8) :
    FiniteGeneratorWord (Fin 8) :=
  positiveWordsTable[j.val * 8 + k.val]!

private def negativeWords (j : Fin 4) (k : Fin 8) :
    FiniteGeneratorWord (Fin 8) :=
  negativeWordsTable[j.val * 8 + k.val]!

private theorem positive_code_checked :
    ∀ (j : Fin 4) (k : Fin 8),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.stateUsed 0 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 4) (k : Fin 8),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.stateUsed 0 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.stateUsed 0 k)))
          (PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 8),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0) =
      PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0 k *
        (PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0 k *
      (PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.stateUsed 0 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 8),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0) =
      (PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0 k *
        PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0 k *
      PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow26NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow26NormalCore.usedCode (PrimitiveAffineSixteenFrameRow26NormalCore.stateUsed 0 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators 0) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalNormalityState0Checks

end
