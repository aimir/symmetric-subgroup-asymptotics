import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityState0Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityState1Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityState2Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityState3Checks


/-! Assembled normality checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityChecks

abbrev Source := PrimitiveAffineSixteenFrameRow2NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

def normality (i : Fin 4) :
    FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient (PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators i) :=
by
  refine Fin.cases PrimitiveAffineSixteenFrameRow2NormalNormalityState0Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow2NormalNormalityState1Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow2NormalNormalityState2Checks.normality ?_ i
  intro i
  exact Fin.cases PrimitiveAffineSixteenFrameRow2NormalNormalityState3Checks.normality (fun i ↦ Fin.elim0 i) i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityChecks

end
