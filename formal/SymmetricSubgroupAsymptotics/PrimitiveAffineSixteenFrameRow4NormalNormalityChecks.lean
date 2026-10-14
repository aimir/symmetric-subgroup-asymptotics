import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityState0Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityState1Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityState2Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityState3Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityState4Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityState5Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityState6Checks


/-! Assembled normality checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityChecks

abbrev Source := PrimitiveAffineSixteenFrameRow4NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow4TopCertificate.group

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow4NormalCore.topAmbient (PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators i) :=
by
  refine Fin.cases PrimitiveAffineSixteenFrameRow4NormalNormalityState0Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow4NormalNormalityState1Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow4NormalNormalityState2Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow4NormalNormalityState3Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow4NormalNormalityState4Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow4NormalNormalityState5Checks.normality ?_ i
  intro i
  exact Fin.cases PrimitiveAffineSixteenFrameRow4NormalNormalityState6Checks.normality (fun i ↦ Fin.elim0 i) i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityChecks

end
