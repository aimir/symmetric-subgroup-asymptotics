import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalCore


/-! Transition checks for normal state 5, classes 11--13.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState5Classes1TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow16NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow16TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient

def classIndex : Fin 3 → Fin 14 :=
  (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (fun i => Fin.elim0 i))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 6) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.parent 3)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow16NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow16NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 6)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 6) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 3) (k : Fin 6) :
    FiniteGeneratorWord (Fin 6) :=
  parentWordsTable[r.val * 6 + k.val]!

def representativeWord (r : Fin 3) : FiniteGeneratorWord (Fin 6) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 3) (k : Fin 6) :
    FiniteNormalJoinWord (Fin 6) Source :=
  childWordsTable[r.val * 6 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 3) (k : Fin 6),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 5 k)) ∧
    (∀ r : Fin 3,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 3) (k : Fin 6),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow16NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 5 q))
          (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow16NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 3) (k : Fin 6),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 3) (k : Fin 6),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 5 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 5 k)
  simpa only [PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 3,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 3) (k : Fin 6),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 5)
        (PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators 5) (PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child 5 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode PrimitiveAffineSixteenFrameRow16NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 5 q))
        (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow16NormalCore.sourceCode PrimitiveAffineSixteenFrameRow16NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.stateUsed 5 q))
            (PrimitiveAffineSixteenFrameRow16NormalCore.usedCode (PrimitiveAffineSixteenFrameRow16NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState5Classes1TransitionChecks

end
