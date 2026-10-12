import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow21NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow21TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow21NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow21NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow21NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow21NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow21NormalCore.topConjugacy

def normality (i : Fin 13) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow21NormalNormalityChecks.normality i

def transition (i : Fin 13) (j : Fin 16) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow21NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow21NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow21NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow21NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow21NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow21NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalCertificate

end
