import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow26NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow26TopCertificate.group

def childWords : Fin 8 → Fin 19 → Fin 8 →
    FiniteNormalJoinWord (Fin 8) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))))

theorem childWords_checked : ∀ (i : Fin 8) (j : Fin 19) (k : Fin 8),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow26NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow26NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow26NormalState7TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalChildTransitionChecks

end
