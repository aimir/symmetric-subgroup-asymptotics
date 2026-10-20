import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow20NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow20TopCertificate.group

def parentWords : Fin 8 → Fin 12 → Fin 7 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))))

def representativeWord : Fin 8 → Fin 12 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))))

theorem parentWords_checked : ∀ (i : Fin 8) (j : Fin 12) (k : Fin 7),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))))

theorem representativeWords_checked : ∀ (i : Fin 8) (j : Fin 12),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalParentTransitionChecks

end
