import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState0Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState1Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState2Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState3Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState4Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState5Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityState6Checks


/-! Assembled normality checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityChecks

abbrev Source := PrimitiveAffineSixteenFrameRow31NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow31TopCertificate.group

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient (PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators i) :=
by
  refine Fin.cases PrimitiveAffineSixteenFrameRow31NormalNormalityState0Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow31NormalNormalityState1Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow31NormalNormalityState2Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow31NormalNormalityState3Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow31NormalNormalityState4Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow31NormalNormalityState5Checks.normality ?_ i
  intro i
  exact Fin.cases PrimitiveAffineSixteenFrameRow31NormalNormalityState6Checks.normality (fun i ↦ Fin.elim0 i) i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityChecks

end
