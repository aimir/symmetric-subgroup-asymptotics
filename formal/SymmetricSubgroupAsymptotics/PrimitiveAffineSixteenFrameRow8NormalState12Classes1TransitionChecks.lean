import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalCore


/-! Transition checks for normal state 12, classes 11--16.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalState12Classes1TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow8NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow8TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient

def classIndex : Fin 6 → Fin 17 :=
  (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (15) (Fin.cases (16) (fun i => Fin.elim0 i)))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 6) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow8NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.parent 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.parent 1))) (FiniteNormalJoinWord.parent 5)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow8NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.parent 0))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.parent 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow8NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2)) (FiniteNormalJoinWord.parent 5)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow8NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.parent 0))) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.parent 5)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow8NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.parent 2))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow8NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 6)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 6) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 6) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  parentWordsTable[r.val * 6 + k.val]!

def representativeWord (r : Fin 6) : FiniteGeneratorWord (Fin 6) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 6) (k : Fin 6) :
    FiniteNormalJoinWord (Fin 6) Source :=
  childWordsTable[r.val * 6 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 6) (k : Fin 6),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 12 k)) ∧
    (∀ r : Fin 6,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 6) (k : Fin 6),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow8NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 12 q))
          (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow8NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 6) (k : Fin 6),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 6) (k : Fin 6),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 12 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 12 k)
  simpa only [PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 6,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow8NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow8NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow8NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 6) (k : Fin 6),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 12)
        (PrimitiveAffineSixteenFrameRow8NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators 12) (PrimitiveAffineSixteenFrameRow8NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow8NormalCore.child 12 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow8NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode PrimitiveAffineSixteenFrameRow8NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 12 q))
        (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow8NormalCore.sourceCode PrimitiveAffineSixteenFrameRow8NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.stateUsed 12 q))
            (PrimitiveAffineSixteenFrameRow8NormalCore.usedCode (PrimitiveAffineSixteenFrameRow8NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalState12Classes1TransitionChecks

end
