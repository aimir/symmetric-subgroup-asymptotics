import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow31NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow31TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow31NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow31NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow31NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow31NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow31NormalCore.topConjugacy

def normality (i : Fin 7) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow31NormalNormalityChecks.normality i

def transition (i : Fin 7) (j : Fin 14) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow31NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow31NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow31NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow31NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow31NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow31NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalCertificate

end
