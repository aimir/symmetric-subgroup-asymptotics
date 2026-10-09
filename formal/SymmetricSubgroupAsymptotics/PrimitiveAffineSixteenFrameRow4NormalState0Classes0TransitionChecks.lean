import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalCore


/-! Transition checks for normal state 0, classes 0--9.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState0Classes0TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow4NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow4TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow4NormalCore.topAmbient

def classIndex : Fin 10 → Fin 10 :=
  (Fin.cases (0) (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 5) Source) :=
  #[FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 3)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 2)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 12))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 12))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 12)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 12))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow4NormalCore.usedSource 1)),FiniteNormalJoinWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 5)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 5) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 10) (k : Fin 5) :
    FiniteGeneratorWord (Fin 5) :=
  parentWordsTable[r.val * 5 + k.val]!

def representativeWord (r : Fin 10) : FiniteGeneratorWord (Fin 5) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 10) (k : Fin 5) :
    FiniteNormalJoinWord (Fin 5) Source :=
  childWordsTable[r.val * 5 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 10) (k : Fin 5),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed 0 k)) ∧
    (∀ r : Fin 10,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 10) (k : Fin 5),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow4NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed 0 q))
          (PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow4NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 10) (k : Fin 5),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 10) (k : Fin 5),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators 0 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators 0 k)
  simpa only [PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 10,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 10) (k : Fin 5),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators 0)
        (PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators 0) (PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow4NormalCore.child 0 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode PrimitiveAffineSixteenFrameRow4NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed 0 q))
        (PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow4NormalCore.sourceCode PrimitiveAffineSixteenFrameRow4NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.stateUsed 0 q))
            (PrimitiveAffineSixteenFrameRow4NormalCore.usedCode (PrimitiveAffineSixteenFrameRow4NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState0Classes0TransitionChecks

end
