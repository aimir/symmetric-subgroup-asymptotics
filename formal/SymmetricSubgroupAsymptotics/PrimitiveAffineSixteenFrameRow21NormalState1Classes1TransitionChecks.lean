import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalCore


/-! Transition checks for normal state 1, classes 11--15.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalState1Classes1TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow21NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow21TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient

def classIndex : Fin 5 → Fin 16 :=
  (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (15) (fun i => Fin.elim0 i))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5)) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 4))]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 7) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 8)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 8)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 2)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 8))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 2))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 8))),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 5)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 5))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1)))) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow21NormalCore.usedSource 1)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 7) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 5) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  parentWordsTable[r.val * 7 + k.val]!

def representativeWord (r : Fin 5) : FiniteGeneratorWord (Fin 7) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 5) (k : Fin 7) :
    FiniteNormalJoinWord (Fin 7) Source :=
  childWordsTable[r.val * 7 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 5) (k : Fin 7),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 1 k)) ∧
    (∀ r : Fin 5,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 5) (k : Fin 7),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow21NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 1 q))
          (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow21NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 5) (k : Fin 7),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 5) (k : Fin 7),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 1 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 1 k)
  simpa only [PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 5,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow21NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow21NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow21NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 5) (k : Fin 7),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 1)
        (PrimitiveAffineSixteenFrameRow21NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators 1) (PrimitiveAffineSixteenFrameRow21NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow21NormalCore.child 1 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow21NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode PrimitiveAffineSixteenFrameRow21NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 1 q))
        (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow21NormalCore.sourceCode PrimitiveAffineSixteenFrameRow21NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.stateUsed 1 q))
            (PrimitiveAffineSixteenFrameRow21NormalCore.usedCode (PrimitiveAffineSixteenFrameRow21NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalState1Classes1TransitionChecks

end
