import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalCore


/-! Normality checks for state 7.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalNormalityState7Checks

abbrev Source := PrimitiveAffineSixteenFrameRow24NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow24TopCertificate.group

private def positiveWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def negativeWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3))) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 3))) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.stateUsed 7 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.ambientUsed j))
            (PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.stateUsed 7 k)))
          (permutationFunctionPairInv
            (PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.ambientUsed j))) := by
  decide +kernel

private theorem negative_code_checked :
    ∀ (j : Fin 4) (k : Fin 8),
      (negativeWords j k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.stateUsed 7 q)) =
        permutationFunctionPairMul
          (permutationFunctionPairMul
            (permutationFunctionPairInv
              (PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.ambientUsed j)))
            (PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.stateUsed 7 k)))
          (PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.ambientUsed j)) := by
  decide +kernel

private theorem positiveWords_checked : ∀ (j : Fin 4) (k : Fin 8),
    (positiveWords j k).eval (PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7) =
      PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7 k *
        (PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j)⁻¹ := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7) (positiveWords j k)
    (PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j * PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7 k *
      (PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j)⁻¹)
  simpa only [PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.stateUsed 7 q))
        (positiveWords j k)).symm.trans (positive_code_checked j k))

private theorem negativeWords_checked : ∀ (j : Fin 4) (k : Fin 8),
    (negativeWords j k).eval (PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7) =
      (PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7 k *
        PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j := by
  intro j k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7) (negativeWords j k)
    ((PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j)⁻¹ * PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7 k *
      PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient j)
  simpa only [PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators_eq_used, PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient_eq_used,
    PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode_encode_used, PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode.encode_mul,
    PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode.encode_inv] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow24NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow24NormalCore.usedCode (PrimitiveAffineSixteenFrameRow24NormalCore.stateUsed 7 q))
        (negativeWords j k)).symm.trans (negative_code_checked j k))

def normality : FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient
    (PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators 7) where
  positiveWords := positiveWords
  positiveEquations := positiveWords_checked
  negativeWords := negativeWords
  negativeEquations := negativeWords_checked

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalNormalityState7Checks

end
