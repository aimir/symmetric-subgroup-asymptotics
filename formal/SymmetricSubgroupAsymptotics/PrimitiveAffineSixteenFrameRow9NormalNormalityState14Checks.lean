import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalCore


/-! Normality checks for state 14.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalNormalityState14Checks

abbrev Source := PrimitiveAffineSixteenFrameRow9NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow9TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 5)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 6)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 5)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6)]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 5)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 6)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 5)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6)]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private def positiveWords (j : Fin 4) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  positiveWordsTable[j.val * 7 + k.val]!

private def negativeWords (j : Fin 4) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  negativeWordsTable[j.val * 7 + k.val]!

private theorem all_code_checked :
    (∀ (j : Fin 4) (k : Fin 7),
      (positiveWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.ambientUsed j)))) ∧
    (∀ (j : Fin 4) (k : Fin 7),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 k)))
          (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 7),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14) =
      PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14 k *
        (PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14 k *
      (PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 q))
        (positiveWords j k)).symm.trans (all_code_checked.1 j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 7),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14) =
      (PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14 k *
        PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14 k *
      PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 q))
        (negativeWords j k)).symm.trans (all_code_checked.2 j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalNormalityState14Checks

end
