import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalState6TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow3NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow3TopCertificate.group

def childWords : Fin 7 → Fin 10 → Fin 5 →
    FiniteNormalJoinWord (Fin 5) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState6TransitionChecks.childWords) (fun i => Fin.elim0 i))))))))

theorem childWords_checked : ∀ (i : Fin 7) (j : Fin 10) (k : Fin 5),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow3NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow3NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow3NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow3NormalState6TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow3NormalChildTransitionChecks

end
