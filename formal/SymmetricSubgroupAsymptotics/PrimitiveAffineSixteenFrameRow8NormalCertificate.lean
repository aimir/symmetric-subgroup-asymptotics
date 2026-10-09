import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow8NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow8TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow8NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow8NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow8NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow8NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow8NormalCore.topConjugacy

def normality (i : Fin 16) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow8NormalNormalityChecks.normality i

def transition (i : Fin 16) (j : Fin 17) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow8NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow8NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow8NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow8NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow8NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow8NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow8NormalCertificate

end
