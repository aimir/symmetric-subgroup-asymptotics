import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow15NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow15TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow15NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow15NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow15NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow15NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow15NormalCore.topConjugacy

def normality (i : Fin 5) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow15NormalNormalityChecks.normality i

def transition (i : Fin 5) (j : Fin 10) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow15NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow15NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow15NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow15NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow15NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow15NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalCertificate

end
