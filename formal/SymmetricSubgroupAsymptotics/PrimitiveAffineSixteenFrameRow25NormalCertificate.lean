import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow25NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow25TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow25NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow25NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow25NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow25NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow25NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow25NormalCore.topConjugacy

def normality (i : Fin 14) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow25NormalNormalityChecks.normality i

def transition (i : Fin 14) (j : Fin 24) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow25NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow25NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalCertificate

end
