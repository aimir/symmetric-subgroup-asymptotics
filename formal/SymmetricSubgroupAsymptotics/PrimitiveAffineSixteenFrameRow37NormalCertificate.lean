import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow37NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow37TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow37NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow37NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow37NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow37NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow37NormalCore.topConjugacy

def normality (i : Fin 6) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow37NormalNormalityChecks.normality i

def transition (i : Fin 6) (j : Fin 17) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow37NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow37NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow37NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow37NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow37NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow37NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalCertificate

end
