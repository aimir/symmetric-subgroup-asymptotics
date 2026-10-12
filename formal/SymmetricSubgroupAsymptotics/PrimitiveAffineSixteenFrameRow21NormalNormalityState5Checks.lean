import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalCore


/-! Normality checks for state 5.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalNormalityState5Checks

abbrev Source := PrimitiveAffineSixteenFrameRow21NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow21TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 5) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  positiveWordsTable[j.val * 7 + k.val]!

private def negativeWords (j : Fin 5) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  negativeWordsTable[j.val * 7 + k.val]!

private theorem positive_code_checked :
    ∀ (j : Fin 5) (k : Fin 7),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 5 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 5 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 5) (k : Fin 7),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 5 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 5 k)))
          (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 5) (k : Fin 7),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5) =
      PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5 k *
        (PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5 k *
      (PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 5 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 5) (k : Fin 7),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5) =
      (PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5 k *
        PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5 k *
      PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 5 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 5) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalNormalityState5Checks

end
