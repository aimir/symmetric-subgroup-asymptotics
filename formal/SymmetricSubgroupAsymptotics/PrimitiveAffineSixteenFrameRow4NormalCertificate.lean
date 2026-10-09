import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow4NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow4TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow4NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow4NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow4NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow4NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow4NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow4NormalCore.topConjugacy

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow4NormalNormalityChecks.normality i

def transition (i : Fin 7) (j : Fin 10) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow4NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow4NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow4NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow4NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow4NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow4NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow4NormalCertificate

end
