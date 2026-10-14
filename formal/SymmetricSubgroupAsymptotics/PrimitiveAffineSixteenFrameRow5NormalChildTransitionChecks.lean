import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalState6TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow5NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

def childWords : Fin 7 → Fin 10 → Fin 5 →
    FiniteNormalJoinWord (Fin 5) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState6TransitionChecks.childWords) (fun i => Fin.elim0 i))))))))

theorem childWords_checked : ∀ (i : Fin 7) (j : Fin 10) (k : Fin 5),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow5NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow5NormalState6TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalChildTransitionChecks

end
