import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow19NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow19TopCertificate.group

def parentWords : Fin 8 → Fin 11 → Fin 6 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))))

def representativeWord : Fin 8 → Fin 11 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))))

theorem parentWords_checked : ∀ (i : Fin 8) (j : Fin 11) (k : Fin 6),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow19NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))))

theorem representativeWords_checked : ∀ (i : Fin 8) (j : Fin 11),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow19NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow19NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalParentTransitionChecks

end
