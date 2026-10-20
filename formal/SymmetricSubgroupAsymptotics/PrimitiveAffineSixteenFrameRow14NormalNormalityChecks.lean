import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState0Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState1Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState2Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState3Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState4Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState5Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityState6Checks


/-! Assembled normality checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityChecks

abbrev Source := PrimitiveAffineSixteenFrameRow14NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow14TopCertificate.group

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow14NormalCore.topAmbient (PrimitiveAffineSixteenFrameRow14NormalCore.stateGenerators i) :=
by
  refine Fin.cases PrimitiveAffineSixteenFrameRow14NormalNormalityState0Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow14NormalNormalityState1Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow14NormalNormalityState2Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow14NormalNormalityState3Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow14NormalNormalityState4Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow14NormalNormalityState5Checks.normality ?_ i
  intro i
  exact Fin.cases PrimitiveAffineSixteenFrameRow14NormalNormalityState6Checks.normality (fun i ↦ Fin.elim0 i) i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow14NormalNormalityChecks

end
