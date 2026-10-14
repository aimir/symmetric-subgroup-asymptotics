import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks


/-! Assembled child transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalChildTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow15NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow15TopCertificate.group

def childWords : Fin 5 → Fin 10 → Fin 5 →
    FiniteNormalJoinWord (Fin 5) Source :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks.childWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks.childWords) (fun i => Fin.elim0 i))))))

theorem childWords_checked : ∀ (i : Fin 5) (j : Fin 10) (k : Fin 5),
    (childWords i j k).eval (parent := PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators i)
        (PrimitiveAffineSixteenFrameRow15NormalCore.topRepresentative j) =
      PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow15NormalCore.child i j) k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks.childWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks.childWords_checked) (fun i => Fin.elim0 i))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalChildTransitionChecks

end
