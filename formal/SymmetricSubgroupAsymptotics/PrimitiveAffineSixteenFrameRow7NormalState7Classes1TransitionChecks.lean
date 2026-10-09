import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalCore


/-! Transition checks for normal state 7, classes 11--16.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalState7Classes1TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow7NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow7TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient

def classIndex : Fin 6 → Fin 17 :=
  (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (15) (Fin.cases (16) (fun i => Fin.elim0 i)))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 6)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5)) (FiniteGeneratorWord.generator 1)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 6) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0)),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.parent 3)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0)))) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow7NormalCore.usedSource 0)))]

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
          (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 7 k)) ∧
    (∀ r : Fin 6,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 6) (k : Fin 6),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow7NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 7 q))
          (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow7NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 6) (k : Fin 6),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 6) (k : Fin 6),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 7 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 7 k)
  simpa only [PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 6,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow7NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow7NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow7NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 6) (k : Fin 6),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 7)
        (PrimitiveAffineSixteenFrameRow7NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators 7) (PrimitiveAffineSixteenFrameRow7NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow7NormalCore.child 7 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow7NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode PrimitiveAffineSixteenFrameRow7NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 7 q))
        (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow7NormalCore.sourceCode PrimitiveAffineSixteenFrameRow7NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.stateUsed 7 q))
            (PrimitiveAffineSixteenFrameRow7NormalCore.usedCode (PrimitiveAffineSixteenFrameRow7NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalState7Classes1TransitionChecks

end
