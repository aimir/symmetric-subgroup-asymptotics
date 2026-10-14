import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalCore


/-! Transition checks for normal state 1, classes 0--7.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState1Classes0TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow2NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient

def classIndex : Fin 8 → Fin 8 :=
  (Fin.cases (0) (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (6) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 4)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 4)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 3)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 4) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 2)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 2)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 2))),FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 1))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow2NormalCore.usedSource 1))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 4)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 4) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 8) (k : Fin 4) :
    FiniteGeneratorWord (Fin 4) :=
  parentWordsTable[r.val * 4 + k.val]!

def representativeWord (r : Fin 8) : FiniteGeneratorWord (Fin 4) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 8) (k : Fin 4) :
    FiniteNormalJoinWord (Fin 4) Source :=
  childWordsTable[r.val * 4 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 8) (k : Fin 4),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 1 k)) ∧
    (∀ r : Fin 8,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 8) (k : Fin 4),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow2NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 1 q))
          (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow2NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 8) (k : Fin 4),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 8) (k : Fin 4),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 1 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 1 k)
  simpa only [PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 8,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 8) (k : Fin 4),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 1)
        (PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 1) (PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 1 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode PrimitiveAffineSixteenFrameRow2NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 1 q))
        (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow2NormalCore.sourceCode PrimitiveAffineSixteenFrameRow2NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.stateUsed 1 q))
            (PrimitiveAffineSixteenFrameRow2NormalCore.usedCode (PrimitiveAffineSixteenFrameRow2NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState1Classes0TransitionChecks

end
