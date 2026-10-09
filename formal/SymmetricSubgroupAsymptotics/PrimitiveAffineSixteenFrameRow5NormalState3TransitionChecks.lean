import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks


/-! Assembled transitions for normal state 3.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState3TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow5NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

def parentWords : Fin 10 → Fin 5 → FiniteGeneratorWord (Fin 5) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 0) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 1) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 2) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 3) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 4) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 5) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 6) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 7) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 8) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords 9) (fun i => Fin.elim0 i)))))))))))

def representativeWord : Fin 10 → FiniteGeneratorWord (Fin 5) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 0) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 1) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 2) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 3) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 4) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 5) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 6) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 7) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 8) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWord 9) (fun i => Fin.elim0 i)))))))))))

def childWords : Fin 10 → Fin 5 →
    FiniteNormalJoinWord (Fin 5) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 0) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 1) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 2) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 3) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 4) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 5) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 6) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 7) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 8) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords 9) (fun i => Fin.elim0 i)))))))))))

theorem parentWords_checked : ∀ (j : Fin 10) (k : Fin 5),
    (parentWords j k).eval (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 3 j)) =
      PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 3 k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 0) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 1) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 2) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 3) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 4) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 5) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 6) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 7) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 8) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.parentWords_checked 9) (fun i => Fin.elim0 i)))))))))))

theorem representativeWords_checked : ∀ j : Fin 10,
    (representativeWord j).eval (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 3 j)) =
      PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 0) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 1) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 2) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 3) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 4) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 5) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 6) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 7) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 8) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.representativeWords_checked 9) (fun i => Fin.elim0 i)))))))))))

theorem childWords_checked : ∀ (j : Fin 10) (k : Fin 5),
    (childWords j k).eval (parent := PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators 3)
        (PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child 3 j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 0) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 1) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 2) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 3) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 4) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 5) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 6) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 7) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 8) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3Classes0TransitionChecks.childWords_checked 9) (fun i => Fin.elim0 i)))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState3TransitionChecks

end
