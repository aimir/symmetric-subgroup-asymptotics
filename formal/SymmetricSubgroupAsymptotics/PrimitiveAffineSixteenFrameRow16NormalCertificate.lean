import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow16NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow16TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow16NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow16NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow16NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow16NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow16NormalCore.topConjugacy

def normality (i : Fin 10) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow16NormalNormalityChecks.normality i

def transition (i : Fin 10) (j : Fin 14) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow16NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow16NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow16NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow16NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow16NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow16NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow16NormalCertificate

end
