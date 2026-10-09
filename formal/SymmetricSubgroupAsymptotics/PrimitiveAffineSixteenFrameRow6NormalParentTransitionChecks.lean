import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow6NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow6TopCertificate.group

def parentWords : Fin 9 → Fin 9 → Fin 6 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks.parentWords) (fun i => Fin.elim0 i))))))))))

def representativeWord : Fin 9 → Fin 9 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks.representativeWord) (fun i => Fin.elim0 i))))))))))

theorem parentWords_checked : ∀ (i : Fin 9) (j : Fin 9) (k : Fin 6),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow6NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i))))))))))

theorem representativeWords_checked : ∀ (i : Fin 9) (j : Fin 9),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow6NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow6NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalParentTransitionChecks

end
