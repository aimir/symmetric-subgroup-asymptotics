import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow19NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow19TopCertificate.group

def childWords : Fin 8 → Fin 11 → Fin 6 →
    FiniteNormalJoinWord (Fin 6) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))))

theorem childWords_checked : ∀ (i : Fin 8) (j : Fin 11) (k : Fin 6),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow19NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow19NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow19NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow19NormalState7TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalChildTransitionChecks

end
