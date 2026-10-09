import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow6NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow6TopCertificate.group

def childWords : Fin 9 → Fin 9 → Fin 6 →
    FiniteNormalJoinWord (Fin 6) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks.childWords) (fun i => Fin.elim0 i))))))))))

theorem childWords_checked : ∀ (i : Fin 9) (j : Fin 9) (k : Fin 6),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow6NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow6NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow6NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState7TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow6NormalState8TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalChildTransitionChecks

end
