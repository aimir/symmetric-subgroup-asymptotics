import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow18NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow18TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow18NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow18NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow18NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow18NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow18NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow18NormalCore.topConjugacy

def normality (i : Fin 8) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow18NormalNormalityChecks.normality i

def transition (i : Fin 8) (j : Fin 11) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow18NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow18NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow18NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow18NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow18NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow18NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow18NormalCertificate

end
