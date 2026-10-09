import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow31NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow31TopCertificate.group

def childWords : Fin 7 → Fin 14 → Fin 6 →
    FiniteNormalJoinWord (Fin 6) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks.childWords) (fun i => Fin.elim0 i))))))))

theorem childWords_checked : ∀ (i : Fin 7) (j : Fin 14) (k : Fin 6),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow31NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow31NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow31NormalState6TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalChildTransitionChecks

end
