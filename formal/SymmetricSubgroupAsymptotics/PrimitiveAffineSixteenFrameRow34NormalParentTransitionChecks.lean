import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState7TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState8TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState9TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalState10TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow34NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow34TopCertificate.group

def parentWords : Fin 11 → Fin 16 → Fin 7 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState7TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState8TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState9TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState10TransitionChecks.parentWords) (fun i => Fin.elim0 i))))))))))))

def representativeWord : Fin 11 → Fin 16 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState7TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState8TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState9TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState10TransitionChecks.representativeWord) (fun i => Fin.elim0 i))))))))))))

theorem parentWords_checked : ∀ (i : Fin 11) (j : Fin 16) (k : Fin 7),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow34NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow34NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow34NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState7TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState8TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState9TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState10TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i))))))))))))

theorem representativeWords_checked : ∀ (i : Fin 11) (j : Fin 16),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow34NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow34NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow34NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState7TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState8TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState9TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow34NormalState10TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalParentTransitionChecks

end
