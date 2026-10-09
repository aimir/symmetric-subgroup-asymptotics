import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow29NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow29TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow29NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow29NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow29NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow29NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow29NormalCore.topConjugacy

def normality (i : Fin 13) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow29NormalNormalityChecks.normality i

def transition (i : Fin 13) (j : Fin 44) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow29NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow29NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow29NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow29NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow29NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow29NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalCertificate

end
