import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow27NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow27TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow27NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow27NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow27NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow27NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow27NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow27NormalCore.topConjugacy

def normality (i : Fin 22) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow27NormalNormalityChecks.normality i

def transition (i : Fin 22) (j : Fin 33) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow27NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow27NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalCertificate

end
