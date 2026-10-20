import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow38NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow38TopCertificate.group

def parentWords : Fin 5 → Fin 19 → Fin 7 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks.parentWords) (fun i => Fin.elim0 i))))))

def representativeWord : Fin 5 → Fin 19 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks.representativeWord) (fun i => Fin.elim0 i))))))

theorem parentWords_checked : ∀ (i : Fin 5) (j : Fin 19) (k : Fin 7),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow38NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow38NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow38NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i))))))

theorem representativeWords_checked : ∀ (i : Fin 5) (j : Fin 19),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow38NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow38NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow38NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalParentTransitionChecks

end
