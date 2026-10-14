import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState0Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState1Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState2Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState3Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState4Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState5Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityState6Checks


/-! Assembled normality checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityChecks

abbrev Source := PrimitiveAffineSixteenFrameRow5NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient (PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators i) :=
by
  refine Fin.cases PrimitiveAffineSixteenFrameRow5NormalNormalityState0Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow5NormalNormalityState1Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow5NormalNormalityState2Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow5NormalNormalityState3Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow5NormalNormalityState4Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow5NormalNormalityState5Checks.normality ?_ i
  intro i
  exact Fin.cases PrimitiveAffineSixteenFrameRow5NormalNormalityState6Checks.normality (fun i ↦ Fin.elim0 i) i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityChecks

end
