import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow17NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow17TopCertificate.group

def parentWords : Fin 10 → Fin 14 → Fin 6 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))))))

def representativeWord : Fin 10 → Fin 14 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))))))

theorem parentWords_checked : ∀ (i : Fin 10) (j : Fin 14) (k : Fin 6),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow17NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))))))

theorem representativeWords_checked : ∀ (i : Fin 10) (j : Fin 14),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow17NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow17NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalParentTransitionChecks

end
