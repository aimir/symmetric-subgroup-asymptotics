import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow26NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow26TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow26NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow26NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow26NormalCore.topConjugacy

def normality (i : Fin 8) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow26NormalNormalityChecks.normality i

def transition (i : Fin 8) (j : Fin 19) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow26NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow26NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalCertificate

end
