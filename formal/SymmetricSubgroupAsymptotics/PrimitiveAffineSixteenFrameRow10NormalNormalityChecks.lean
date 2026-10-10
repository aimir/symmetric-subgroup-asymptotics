import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityState0Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityState1Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityState2Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityState3Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityState4Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityState5Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityState6Checks


/-! Assembled normality checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityChecks

abbrev Source := PrimitiveAffineSixteenFrameRow10NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow10TopCertificate.group

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow10NormalCore.topAmbient (PrimitiveAffineSixteenFrameRow10NormalCore.stateGenerators i) :=
by
  refine Fin.cases PrimitiveAffineSixteenFrameRow10NormalNormalityState0Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow10NormalNormalityState1Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow10NormalNormalityState2Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow10NormalNormalityState3Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow10NormalNormalityState4Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow10NormalNormalityState5Checks.normality ?_ i
  intro i
  exact Fin.cases PrimitiveAffineSixteenFrameRow10NormalNormalityState6Checks.normality (fun i ↦ Fin.elim0 i) i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityChecks

end
