import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow10NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow10TopCertificate.group

def parentWords : Fin 7 → Fin 14 → Fin 7 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks.parentWords) (fun i => Fin.elim0 i))))))))

def representativeWord : Fin 7 → Fin 14 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks.representativeWord) (fun i => Fin.elim0 i))))))))

theorem parentWords_checked : ∀ (i : Fin 7) (j : Fin 14) (k : Fin 7),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow10NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow10NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow10NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i))))))))

theorem representativeWords_checked : ∀ (i : Fin 7) (j : Fin 14),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow10NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow10NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow10NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalParentTransitionChecks

end
