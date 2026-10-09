import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow2NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

def parentWords : Fin 4 → Fin 8 → Fin 4 →
    FiniteGeneratorWord (Fin 4) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))

def representativeWord : Fin 4 → Fin 8 →
    FiniteGeneratorWord (Fin 4) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))

theorem parentWords_checked : ∀ (i : Fin 4) (j : Fin 8) (k : Fin 4),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))

theorem representativeWords_checked : ∀ (i : Fin 4) (j : Fin 8),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalParentTransitionChecks

end
