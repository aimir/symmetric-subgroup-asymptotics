import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow24NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow24TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow24NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow24NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow24NormalCore.topConjugacy

def normality (i : Fin 8) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow24NormalNormalityChecks.normality i

def transition (i : Fin 8) (j : Fin 19) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks.childWords_checked i j

private theorem bottom_eq :
    Subgroup.closure (Set.range (stateGenerators 0)) = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> rfl
  · exact bot_le

noncomputable def data : FiniteNormalJoinWordRegistryData
    topConjugacy.toCardinalCover topAmbient stateGenerators where
  ambient_full := topAmbient_full
  normality := normality
  bottom := 0
  bottom_eq := bottom_eq
  child := child
  transition := transition

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  data.complete N

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalCertificate

end
