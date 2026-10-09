import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow2NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

def childWords : Fin 4 → Fin 8 → Fin 4 →
    FiniteNormalJoinWord (Fin 4) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks.childWords) (fun i => Fin.elim0 i)))))

theorem childWords_checked : ∀ (i : Fin 4) (j : Fin 8) (k : Fin 4),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow2NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow2NormalState3TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalChildTransitionChecks

end
