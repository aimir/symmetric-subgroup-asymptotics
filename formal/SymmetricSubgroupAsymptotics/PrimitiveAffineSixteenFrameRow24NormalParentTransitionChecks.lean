import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks


/-! Assembled parent and representative transition checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks

abbrev Source := PrimitiveAffineSixteenFrameRow24NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow24TopCertificate.group

def parentWords : Fin 8 → Fin 19 → Fin 8 →
    FiniteGeneratorWord (Fin 8) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks.parentWords) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks.parentWords) (fun i => Fin.elim0 i)))))))))

def representativeWord : Fin 8 → Fin 19 →
    FiniteGeneratorWord (Fin 8) :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks.representativeWord) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks.representativeWord) (fun i => Fin.elim0 i)))))))))

theorem parentWords_checked : ∀ (i : Fin 8) (j : Fin 19) (k : Fin 8),
    (parentWords i j k).eval (PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow24NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators i k :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks.parentWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks.parentWords_checked) (fun i => Fin.elim0 i)))))))))

theorem representativeWords_checked : ∀ (i : Fin 8) (j : Fin 19),
    (representativeWord i j).eval (PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators (PrimitiveAffineSixteenFrameRow24NormalCore.child i j)) =
      PrimitiveAffineSixteenFrameRow24NormalCore.topRepresentative j :=
  (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState0TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState1TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState2TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState3TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState4TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState5TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState6TransitionChecks.representativeWords_checked) (Fin.cases (PrimitiveAffineSixteenFrameRow24NormalState7TransitionChecks.representativeWords_checked) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks

end
