import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks


/-! Assembled transitions for normal state 3.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow2NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

def parentWords : Fin 8 → Fin 4 → FiniteGeneratorWord (Fin 4) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 0) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 1) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 2) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 3) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 4) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 5) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 6) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords 7) (fun i => Fin.elim0 i)))))))))

def representativeWord : Fin 8 → FiniteGeneratorWord (Fin 4) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 0) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 1) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 2) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 3) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 4) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 5) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 6) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWord 7) (fun i => Fin.elim0 i)))))))))

def childWords : Fin 8 → Fin 4 →
    FiniteNormalJoinWord (Fin 4) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 0) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 1) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 2) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 3) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 4) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 5) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 6) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords 7) (fun i => Fin.elim0 i)))))))))

theorem parentWords_checked : ∀ (j : Fin 8) (k : Fin 4),
    (parentWords j k).eval (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 3 j)) =
      PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 3 k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 0) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 1) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 2) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 3) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 4) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 5) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 6) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.parentWords_checked 7) (fun i => Fin.elim0 i)))))))))

theorem representativeWords_checked : ∀ j : Fin 8,
    (representativeWord j).eval (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 3 j)) =
      PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 0) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 1) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 2) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 3) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 4) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 5) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 6) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.representativeWords_checked 7) (fun i => Fin.elim0 i)))))))))

theorem childWords_checked : ∀ (j : Fin 8) (k : Fin 4),
    (childWords j k).eval (parent := PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators 3)
        (PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child 3 j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 0) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 1) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 2) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 3) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 4) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 5) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 6) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3Classes0TransitionChecks.childWords_checked 7) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks

end
