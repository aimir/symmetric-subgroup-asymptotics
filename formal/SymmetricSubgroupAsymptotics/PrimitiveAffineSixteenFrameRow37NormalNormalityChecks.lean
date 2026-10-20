import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState0Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState1Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState2Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState3Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState4Checks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityState5Checks


/-! Assembled normality checks.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityChecks

abbrev Source := PrimitiveAffineSixteenFrameRow37NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow37TopCertificate.group

def normality (i : Fin 6) :
    FiniteNormalityWordCertificate PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient (PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators i) :=
by
  refine Fin.cases PrimitiveAffineSixteenFrameRow37NormalNormalityState0Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow37NormalNormalityState1Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow37NormalNormalityState2Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow37NormalNormalityState3Checks.normality ?_ i
  intro i
  refine Fin.cases PrimitiveAffineSixteenFrameRow37NormalNormalityState4Checks.normality ?_ i
  intro i
  exact Fin.cases PrimitiveAffineSixteenFrameRow37NormalNormalityState5Checks.normality (fun i ↦ Fin.elim0 i) i

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityChecks

end
