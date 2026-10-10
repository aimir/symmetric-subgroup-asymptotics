import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow12NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow12TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow12NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow12NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow12NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow12NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow12NormalCore.topConjugacy

def normality (i : Fin 15) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow12NormalNormalityChecks.normality i

def transition (i : Fin 15) (j : Fin 28) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow12NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow12NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow12NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow12NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow12NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow12NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalCertificate

end
