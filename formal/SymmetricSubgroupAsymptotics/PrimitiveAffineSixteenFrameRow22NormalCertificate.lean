import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow22NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow22TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow22NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow22NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow22NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow22NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow22NormalCore.topConjugacy

def normality (i : Fin 13) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow22NormalNormalityChecks.normality i

def transition (i : Fin 13) (j : Fin 16) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow22NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow22NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow22NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow22NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow22NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow22NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalCertificate

end
