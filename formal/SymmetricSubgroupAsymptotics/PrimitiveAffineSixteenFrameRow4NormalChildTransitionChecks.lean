import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalState6TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow4NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow4TopCertificate.group

def childWords : Fin 7 → Fin 10 → Fin 5 →
    FiniteNormalJoinWord (Fin 5) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState6TransitionChecks.childWords) (fun i => Fin.elim0 i))))))))

theorem childWords_checked : ∀ (i : Fin 7) (j : Fin 10) (k : Fin 5),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow4NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow4NormalState6TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalChildTransitionChecks

end
