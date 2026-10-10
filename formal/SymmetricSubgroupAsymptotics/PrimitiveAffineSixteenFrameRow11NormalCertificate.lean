import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow11NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow11TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow11NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow11NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow11NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow11NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow11NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow11NormalCore.topConjugacy

def normality (i : Fin 41) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow11NormalNormalityChecks.normality i

def transition (i : Fin 41) (j : Fin 36) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow11NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow11NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow11NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow11NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow11NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow11NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11NormalCertificate

end
