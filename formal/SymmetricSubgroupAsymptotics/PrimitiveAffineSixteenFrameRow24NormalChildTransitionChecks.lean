import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow24NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow24TopCertificate.group

def childWords : Fin 8 → Fin 19 → Fin 8 →
    FiniteNormalJoinWord (Fin 8) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))))

theorem childWords_checked : ∀ (i : Fin 8) (j : Fin 19) (k : Fin 8),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow24NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow24NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks

end
