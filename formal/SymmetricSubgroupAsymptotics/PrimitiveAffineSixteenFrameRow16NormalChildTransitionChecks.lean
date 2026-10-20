import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow16NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow16TopCertificate.group

def childWords : Fin 10 → Fin 14 → Fin 6 →
    FiniteNormalJoinWord (Fin 6) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))))))

theorem childWords_checked : ∀ (i : Fin 10) (j : Fin 14) (k : Fin 6),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow16NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState7TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState8TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow16NormalState9TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalChildTransitionChecks

end
