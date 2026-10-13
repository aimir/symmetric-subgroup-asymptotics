import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow26NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow26TopCertificate.group

def parentWords : Fin 8 → Fin 19 → Fin 8 →
    FiniteGeneratorWord (Fin 8) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))))

def representativeWord : Fin 8 → Fin 19 →
    FiniteGeneratorWord (Fin 8) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))))

theorem parentWords_checked : ∀ (i : Fin 8) (j : Fin 19) (k : Fin 8),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow26NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))))

theorem representativeWords_checked : ∀ (i : Fin 8) (j : Fin 19),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow26NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow26NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks

end
