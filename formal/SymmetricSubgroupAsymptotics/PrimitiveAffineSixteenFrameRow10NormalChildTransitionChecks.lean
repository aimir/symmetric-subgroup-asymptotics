import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow10NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow10TopCertificate.group

def childWords : Fin 7 → Fin 14 → Fin 7 →
    FiniteNormalJoinWord (Fin 7) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks.childWords) (fun i => Fin.elim0 i))))))))

theorem childWords_checked : ∀ (i : Fin 7) (j : Fin 14) (k : Fin 7),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow10NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow10NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow10NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow10NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow10NormalState6TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalChildTransitionChecks

end
