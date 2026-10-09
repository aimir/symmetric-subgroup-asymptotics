import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow31NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow31TopCertificate.group

def parentWords : Fin 7 → Fin 14 → Fin 6 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks.parentWords) (fun i => Fin.elim0 i))))))))

def representativeWord : Fin 7 → Fin 14 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks.representativeWord) (fun i => Fin.elim0 i))))))))

theorem parentWords_checked : ∀ (i : Fin 7) (j : Fin 14) (k : Fin 6),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow31NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i))))))))

theorem representativeWords_checked : ∀ (i : Fin 7) (j : Fin 14),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow31NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow31NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalParentTransitionChecks

end
