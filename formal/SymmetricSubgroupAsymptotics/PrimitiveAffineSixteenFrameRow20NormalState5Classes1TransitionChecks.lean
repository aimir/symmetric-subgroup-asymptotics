import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalCore


/-! Transition checks for normal state 5, classes 11--11.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState5Classes1TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow20NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow20TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow20NormalCore.topAmbient

def classIndex : Fin 1 → Fin 12 :=
  (Fin.cases (11) (fun i => Fin.elim0 i))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 3)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 7) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow20NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow20NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow20NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow20NormalCore.usedSource 1)))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow20NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.parent 2)) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow20NormalCore.usedSource 1))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow20NormalCore.usedSource 1)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2)) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 7) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 1) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  parentWordsTable[r.val * 7 + k.val]!

def representativeWord (r : Fin 1) : FiniteGeneratorWord (Fin 7) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 1) (k : Fin 7) :
    FiniteNormalJoinWord (Fin 7) Source :=
  childWordsTable[r.val * 7 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 1) (k : Fin 7),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 5 k)) ∧
    (∀ r : Fin 1,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 1) (k : Fin 7),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow20NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 5 q))
          (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow20NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 1) (k : Fin 7),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 1) (k : Fin 7),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 5 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 5 k)
  simpa only [PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 1,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 1) (k : Fin 7),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 5)
        (PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators 5) (PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child 5 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode PrimitiveAffineSixteenFrameRow20NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 5 q))
        (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow20NormalCore.sourceCode PrimitiveAffineSixteenFrameRow20NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.stateUsed 5 q))
            (PrimitiveAffineSixteenFrameRow20NormalCore.usedCode (PrimitiveAffineSixteenFrameRow20NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState5Classes1TransitionChecks

end
