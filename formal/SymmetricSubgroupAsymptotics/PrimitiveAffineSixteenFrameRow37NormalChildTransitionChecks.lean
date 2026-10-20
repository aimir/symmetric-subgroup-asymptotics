import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow37NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow37TopCertificate.group

def childWords : Fin 6 → Fin 17 → Fin 7 →
    FiniteNormalJoinWord (Fin 7) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))

theorem childWords_checked : ∀ (i : Fin 6) (j : Fin 17) (k : Fin 7),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow37NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow37NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow37NormalState5TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalChildTransitionChecks

end
