import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow18NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow18TopCertificate.group

def childWords : Fin 8 → Fin 11 → Fin 6 →
    FiniteNormalJoinWord (Fin 6) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))))

theorem childWords_checked : ∀ (i : Fin 8) (j : Fin 11) (k : Fin 6),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow18NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow18NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow18NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow18NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow18NormalState7TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalChildTransitionChecks

end
