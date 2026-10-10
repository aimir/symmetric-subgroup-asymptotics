import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalCore


/-! Transition checks for normal state 14, classes 22--27.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalState14Classes2TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow12NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow12TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient

def classIndex : Fin 6 → Fin 28 :=
  (Fin.cases (22) (Fin.cases (23) (Fin.cases (24) (Fin.cases (25) (Fin.cases (26) (Fin.cases (27) (fun i => Fin.elim0 i)))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one,FiniteGeneratorWord.one]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 8)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 1))) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 0))) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2))) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.inv (FiniteGeneratorWord.generator 2)),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 0)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 8) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one,FiniteNormalJoinWord.one]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 8)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 8) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 6) (k : Fin 8) :
    FiniteGeneratorWord (Fin 8) :=
  parentWordsTable[r.val * 8 + k.val]!

def representativeWord (r : Fin 6) : FiniteGeneratorWord (Fin 8) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 6) (k : Fin 8) :
    FiniteNormalJoinWord (Fin 8) Source :=
  childWordsTable[r.val * 8 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 6) (k : Fin 8),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 14 k)) ∧
    (∀ r : Fin 6,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 6) (k : Fin 8),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow12NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 14 q))
          (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow12NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 6) (k : Fin 8),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 6) (k : Fin 8),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 14 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 14 k)
  simpa only [PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 6,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow12NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow12NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow12NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 6) (k : Fin 8),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 14)
        (PrimitiveAffineSixteenFrameRow12NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators 14) (PrimitiveAffineSixteenFrameRow12NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow12NormalCore.child 14 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow12NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode PrimitiveAffineSixteenFrameRow12NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 14 q))
        (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow12NormalCore.sourceCode PrimitiveAffineSixteenFrameRow12NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.stateUsed 14 q))
            (PrimitiveAffineSixteenFrameRow12NormalCore.usedCode (PrimitiveAffineSixteenFrameRow12NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalState14Classes2TransitionChecks

end
