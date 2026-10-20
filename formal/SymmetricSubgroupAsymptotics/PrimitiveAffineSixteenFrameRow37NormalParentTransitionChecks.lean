import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow37NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow37TopCertificate.group

def parentWords : Fin 6 → Fin 17 → Fin 7 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))

def representativeWord : Fin 6 → Fin 17 →
    FiniteGeneratorWord (Fin 7) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))

theorem parentWords_checked : ∀ (i : Fin 6) (j : Fin 17) (k : Fin 7),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow37NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))

theorem representativeWords_checked : ∀ (i : Fin 6) (j : Fin 17),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow37NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow37NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalParentTransitionChecks

end
