import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow18NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow18TopCertificate.group

def parentWords : Fin 8 → Fin 11 → Fin 6 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))))

def representativeWord : Fin 8 → Fin 11 →
    FiniteGeneratorWord (Fin 6) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))))

theorem parentWords_checked : ∀ (i : Fin 8) (j : Fin 11) (k : Fin 6),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow18NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow18NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow18NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))))

theorem representativeWords_checked : ∀ (i : Fin 8) (j : Fin 11),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow18NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow18NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow18NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalParentTransitionChecks

end
