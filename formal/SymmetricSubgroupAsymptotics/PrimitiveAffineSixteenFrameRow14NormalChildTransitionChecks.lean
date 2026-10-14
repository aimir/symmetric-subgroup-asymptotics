import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow14NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow14TopCertificate.group

def childWords : Fin 7 → Fin 10 → Fin 5 →
    FiniteNormalJoinWord (Fin 5) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks.childWords) (fun i => Fin.elim0 i))))))))

theorem childWords_checked : ∀ (i : Fin 7) (j : Fin 10) (k : Fin 5),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow14NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow14NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow14NormalState6TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalChildTransitionChecks

end
