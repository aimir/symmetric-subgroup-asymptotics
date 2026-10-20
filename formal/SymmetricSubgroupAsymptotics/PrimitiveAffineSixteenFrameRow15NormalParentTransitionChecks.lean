import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow15NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow15TopCertificate.group

def parentWords : Fin 5 → Fin 10 → Fin 5 →
    FiniteGeneratorWord (Fin 5) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks.parentWords) (fun i => Fin.elim0 i))))))

def representativeWord : Fin 5 → Fin 10 →
    FiniteGeneratorWord (Fin 5) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks.representativeWord) (fun i => Fin.elim0 i))))))

theorem parentWords_checked : ∀ (i : Fin 5) (j : Fin 10) (k : Fin 5),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow15NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i))))))

theorem representativeWords_checked : ∀ (i : Fin 5) (j : Fin 10),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow15NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow15NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow15NormalState4TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalParentTransitionChecks

end
