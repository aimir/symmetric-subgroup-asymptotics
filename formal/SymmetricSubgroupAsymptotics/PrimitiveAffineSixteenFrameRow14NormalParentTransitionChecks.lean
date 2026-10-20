import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow14NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow14TopCertificate.group

def parentWords : Fin 7 → Fin 10 → Fin 5 →
    FiniteGeneratorWord (Fin 5) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks.parentWords) (fun i => Fin.elim0 i))))))))

def representativeWord : Fin 7 → Fin 10 →
    FiniteGeneratorWord (Fin 5) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks.representativeWord) (fun i => Fin.elim0 i))))))))

theorem parentWords_checked : ∀ (i : Fin 7) (j : Fin 10) (k : Fin 5),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow14NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i))))))))

theorem representativeWords_checked : ∀ (i : Fin 7) (j : Fin 10),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow14NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow14NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalParentTransitionChecks

end
