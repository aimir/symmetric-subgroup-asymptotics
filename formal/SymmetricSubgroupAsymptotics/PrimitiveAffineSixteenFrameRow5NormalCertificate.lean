import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow5NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow5NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow5NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow5NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow5NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow5NormalCore.topConjugacy

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow5NormalNormalityChecks.normality i

def transition (i : Fin 7) (j : Fin 10) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow5NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow5NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow5NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow5NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow5NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow5NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalCertificate

end
