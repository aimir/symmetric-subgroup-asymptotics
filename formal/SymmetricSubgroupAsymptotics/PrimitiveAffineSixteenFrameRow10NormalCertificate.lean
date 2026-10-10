import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow10NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow10TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow10NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow10NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow10NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow10NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow10NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow10NormalCore.topConjugacy

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow10NormalNormalityChecks.normality i

def transition (i : Fin 7) (j : Fin 14) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow10NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow10NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow10NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow10NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow10NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow10NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalCertificate

end
