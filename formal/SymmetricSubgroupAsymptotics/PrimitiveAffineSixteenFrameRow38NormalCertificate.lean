import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow38NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow38TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow38NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow38NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow38NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow38NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow38NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow38NormalCore.topConjugacy

def normality (i : Fin 5) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow38NormalNormalityChecks.normality i

def transition (i : Fin 5) (j : Fin 19) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow38NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow38NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow38NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow38NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow38NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow38NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalCertificate

end
