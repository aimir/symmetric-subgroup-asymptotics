import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23NormalCore


/-! Transition checks for normal state 8, classes 22--23.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23NormalState8Classes2TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow23NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow23TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow23NormalCore.topAmbient

def classIndex : Fin 2 → Fin 24 :=
  (Fin.cases (22) (Fin.cases (23) (fun i => Fin.elim0 i)))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 4)) (FiniteGeneratorWord.generator 3)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 8) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0)))) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))) (FiniteNormalJoinWord.parent 3)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2))) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1)) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0)),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2)))) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 2))),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))) (FiniteNormalJoinWord.parent 4)) (FiniteNormalJoinWord.inv (FiniteNormalJoinWord.conjugate (PrimitiveAffineSixteenFrameRow23NormalCore.usedSource 0))),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 8)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 8) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 2) (k : Fin 8) :
    FiniteGeneratorWord (Fin 8) :=
  parentWordsTable[r.val * 8 + k.val]!

def representativeWord (r : Fin 2) : FiniteGeneratorWord (Fin 8) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 2) (k : Fin 8) :
    FiniteNormalJoinWord (Fin 8) Source :=
  childWordsTable[r.val * 8 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 2) (k : Fin 8),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed 8 k)) ∧
    (∀ r : Fin 2,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 2) (k : Fin 8),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow23NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed 8 q))
          (PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow23NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 2) (k : Fin 8),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 2) (k : Fin 8),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators 8 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators 8 k)
  simpa only [PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 2,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow23NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow23NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow23NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 2) (k : Fin 8),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators 8)
        (PrimitiveAffineSixteenFrameRow23NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators 8) (PrimitiveAffineSixteenFrameRow23NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow23NormalCore.child 8 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow23NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow23NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode PrimitiveAffineSixteenFrameRow23NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed 8 q))
        (PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow23NormalCore.sourceCode PrimitiveAffineSixteenFrameRow23NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.stateUsed 8 q))
            (PrimitiveAffineSixteenFrameRow23NormalCore.usedCode (PrimitiveAffineSixteenFrameRow23NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23NormalState8Classes2TransitionChecks

end
