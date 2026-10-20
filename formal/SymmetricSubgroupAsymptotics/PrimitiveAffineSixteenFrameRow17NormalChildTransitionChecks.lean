import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow17NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow17TopCertificate.group

def childWords : Fin 10 → Fin 14 → Fin 6 →
    FiniteNormalJoinWord (Fin 6) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks.childWords) (fun i => Fin.elim0 i)))))))))))

theorem childWords_checked : ∀ (i : Fin 10) (j : Fin 14) (k : Fin 6),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow17NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow17NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState4TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState5TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState6TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState7TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState8TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow17NormalState9TransitionChecks.childWords_checked) (fun i => Fin.elim0 i)))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalChildTransitionChecks

end
