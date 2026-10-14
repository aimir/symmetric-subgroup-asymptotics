import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow38NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow38TopCertificate.group

def childWords : Fin 5 → Fin 19 → Fin 7 →
    FiniteNormalJoinWord (Fin 7) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks.childWords) (fun i => Fin.elim0 i))))))

theorem childWords_checked : ∀ (i : Fin 5) (j : Fin 19) (k : Fin 7),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow38NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow38NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow38NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow38NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow38NormalState4TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalChildTransitionChecks

end
