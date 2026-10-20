import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow16NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow16TopCertificate.group

def parentWords : Fin 10 → Fin 14 → Fin 6 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))))))

def representativeWord : Fin 10 → Fin 14 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))))))

theorem parentWords_checked : ∀ (i : Fin 10) (j : Fin 14) (k : Fin 6),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))))))

theorem representativeWords_checked : ∀ (i : Fin 10) (j : Fin 14),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalParentTransitionChecks

end
