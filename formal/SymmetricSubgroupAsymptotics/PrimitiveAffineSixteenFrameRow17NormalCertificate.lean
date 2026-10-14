import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow17NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow17TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow17NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow17NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow17NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow17NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow17NormalCore.topConjugacy

def normality (i : Fin 10) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow17NormalNormalityChecks.normality i

def transition (i : Fin 10) (j : Fin 14) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow17NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow17NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow17NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow17NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow17NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow17NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalCertificate

end
