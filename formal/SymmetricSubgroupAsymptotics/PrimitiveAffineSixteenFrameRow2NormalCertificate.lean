import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow2NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow2NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow2NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow2NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow2NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow2NormalCore.topConjugacy

def normality (i : Fin 4) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow2NormalNormalityChecks.normality i

def transition (i : Fin 4) (j : Fin 8) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow2NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow2NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow2NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow2NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow2NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow2NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalCertificate

end
