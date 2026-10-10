import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalCore


/-! Transition checks for normal state 14, classes 11--17.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalState14Classes1TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow9NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow9TopCertificate.group
abbrev topAmbient := PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient

def classIndex : Fin 7 → Fin 18 :=
  (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (15) (Fin.cases (16) (Fin.cases (17) (fun i => Fin.elim0 i))))))))

private def parentWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 1),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 4),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 5),FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 6)]

private def representativeWordsTable : Array (FiniteGeneratorWord (Fin 7)) :=
  #[FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 6),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3),FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.mul (FiniteGeneratorWord.one) (FiniteGeneratorWord.generator 0)) (FiniteGeneratorWord.generator 2)) (FiniteGeneratorWord.generator 3)) (FiniteGeneratorWord.generator 6)]

private def childWordsTable : Array (FiniteNormalJoinWord (Fin 7) Source) :=
  #[FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 6),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 6),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 6),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 6),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 6),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 6),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 0),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 1),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 2),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 3),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 4),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 5),FiniteNormalJoinWord.mul (FiniteNormalJoinWord.one) (FiniteNormalJoinWord.parent 6)]

private instance finiteGeneratorWordInhabited :
    Inhabited (FiniteGeneratorWord (Fin 7)) :=
  ⟨FiniteGeneratorWord.one⟩

private instance finiteNormalJoinWordInhabited :
    Inhabited (FiniteNormalJoinWord (Fin 7) Source) :=
  ⟨FiniteNormalJoinWord.one⟩

def parentWords (r : Fin 7) (k : Fin 7) :
    FiniteGeneratorWord (Fin 7) :=
  parentWordsTable[r.val * 7 + k.val]!

def representativeWord (r : Fin 7) : FiniteGeneratorWord (Fin 7) :=
  representativeWordsTable[r.val]!

def childWords (r : Fin 7) (k : Fin 7) :
    FiniteNormalJoinWord (Fin 7) Source :=
  childWordsTable[r.val * 7 + k.val]!

private theorem all_code_checked :
    (∀ (r : Fin 7) (k : Fin 7),
      (parentWords r k).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 k)) ∧
    (∀ r : Fin 7,
      (representativeWord r).evalCodeOps (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv
          (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode
            (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)) q)) =
        PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.representativeUsed (classIndex r))) ∧
    (∀ (r : Fin 7) (k : Fin 7),
      (childWords r k).evalCodeOpsWith (permutationFunctionPairOne 16)
          permutationFunctionPairMul permutationFunctionPairInv PrimitiveAffineSixteenFrameRow9NormalCore.usedEncode
          (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 q))
          (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.representativeUsed (classIndex r))) =
        PrimitiveAffineSixteenFrameRow9NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)) k)) := by
  decide +kernel

private theorem childConjugators_checked : ∀ (r : Fin 7) (k : Fin 7),
    (childWords r k).ConjugatorsSatisfy
      (fun g ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedEncode g = PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode.encode g) := by
  intro r k
  fin_cases r <;> fin_cases k <;>
    simp [childWords, childWordsTable,
      FiniteNormalJoinWord.ConjugatorsSatisfy]

theorem parentWords_checked : ∀ (r : Fin 7) (k : Fin 7),
    (parentWords r k).eval
        (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14 k := by
  intro r k
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)))
    (parentWords r k) (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14 k)
  simpa only [PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)) q))
        (parentWords r k)).symm.trans (all_code_checked.1 r k))

theorem representativeWords_checked : ∀ r : Fin 7,
    (representativeWord r).eval
        (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r))) =
      PrimitiveAffineSixteenFrameRow9NormalCore.topRepresentative (classIndex r) := by
  intro r
  apply FiniteGeneratorWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)))
    (representativeWord r) (PrimitiveAffineSixteenFrameRow9NormalCore.topRepresentative (classIndex r))
  simpa only [PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow9NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode_encode_used] using
      ((FiniteGeneratorWord.evalCodeOps_eq_evalCode PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
        (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode
          (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)) q))
        (representativeWord r)).symm.trans (all_code_checked.2.1 r))

theorem childWords_checked : ∀ (r : Fin 7) (k : Fin 7),
    (childWords r k).eval (parent := PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14)
        (PrimitiveAffineSixteenFrameRow9NormalCore.topRepresentative (classIndex r)) =
      PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)) k := by
  intro r k
  apply FiniteNormalJoinWord.eq_of_evalCode_eq PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode
    (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators 14) (PrimitiveAffineSixteenFrameRow9NormalCore.topRepresentative (classIndex r))
    (childWords r k)
    (PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow9NormalCore.child 14 (classIndex r)) k)
  simpa only [PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators_eq_used,
    PrimitiveAffineSixteenFrameRow9NormalCore.topRepresentative_eq_used,
    PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode_encode_used] using
      ((FiniteNormalJoinWord.evalCodeWith_eq PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode PrimitiveAffineSixteenFrameRow9NormalCore.usedEncode
        (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 q))
        (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.representativeUsed (classIndex r)))
        (childWords r k) (childConjugators_checked r k)).symm.trans
          ((FiniteNormalJoinWord.evalCodeOpsWith_eq_evalCodeWith
            PrimitiveAffineSixteenFrameRow9NormalCore.sourceCode PrimitiveAffineSixteenFrameRow9NormalCore.usedEncode
            (fun q ↦ PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.stateUsed 14 q))
            (PrimitiveAffineSixteenFrameRow9NormalCore.usedCode (PrimitiveAffineSixteenFrameRow9NormalCore.representativeUsed (classIndex r)))
            (childWords r k)).symm.trans (all_code_checked.2.2 r k)))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalState14Classes1TransitionChecks

end
