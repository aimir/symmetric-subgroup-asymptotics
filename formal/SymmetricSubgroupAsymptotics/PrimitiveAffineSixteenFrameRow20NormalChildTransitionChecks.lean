import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow20NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow20TopCertificate.group

def childWords : Fin 8 → Fin 12 → Fin 7 →
    FiniteNormalJoinWord (Fin 7) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))))

theorem childWords_checked : ∀ (i : Fin 8) (j : Fin 12) (k : Fin 7),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow20NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow20NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow20NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow20NormalState7TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalChildTransitionChecks

end
