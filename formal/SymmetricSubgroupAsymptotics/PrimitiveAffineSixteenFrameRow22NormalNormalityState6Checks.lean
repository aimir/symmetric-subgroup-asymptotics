import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalCore


/-! Normality checks for state 6.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalNormalityState6Checks

abbrev Source := PrimitiveAffineSixteenFrameRow22NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow22TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 4) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  positiveWordsTable[j.val * 7 + k.val]!

private def negativeWords (j : Fin 4) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  negativeWordsTable[j.val * 7 + k.val]!

private theorem positive_code_checked :
    ∀ (j : Fin 4) (k : Fin 7),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.stateUsed 6 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.stateUsed 6 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 4) (k : Fin 7),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.stateUsed 6 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.stateUsed 6 k)))
          (PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 7),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6) =
      PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6 k *
        (PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6 k *
      (PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.stateUsed 6 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 7),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6) =
      (PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6 k *
        PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6 k *
      PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow22NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow22NormalCore.usedCode (PrimitiveAffineSixteenFrameRow22NormalCore.stateUsed 6 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators 6) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalNormalityState6Checks

end
