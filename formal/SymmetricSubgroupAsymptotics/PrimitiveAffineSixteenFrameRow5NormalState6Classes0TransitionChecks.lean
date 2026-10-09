import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalCore


/-! Transition checks for normal state 6, classes 0--9.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState6Classes0TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow5NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient

def classIndex : Fin 10 → Fin 10 :=
  (Fin.cases (0) (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 5)) :=
  #[FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 5) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 6 k)) ∧
    (∀ r : Fin 10,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 10) (k : Fin 5),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow5NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 6 q))
          (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow5NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 10) (k : Fin 5),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 10) (k : Fin 5),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 6 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 6 k)
  simpa only [PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 10,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 10) (k : Fin 5),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 6)
        (PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 6) (PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 6 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode PrimitiveAffineSixteenFrameRow5NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 6 q))
        (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow5NormalCore.sourceCode PrimitiveAffineSixteenFrameRow5NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.stateUsed 6 q))
            (PrimitiveAffineSixteenFrameRow5NormalCore.usedCode (PrimitiveAffineSixteenFrameRow5NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState6Classes0TransitionChecks

end
