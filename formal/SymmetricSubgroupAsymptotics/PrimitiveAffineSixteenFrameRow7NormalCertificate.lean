import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow7NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow7TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow7NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow7NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow7NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow7NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow7NormalCore.topConjugacy

def normality (i : Fin 16) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow7NormalNormalityChecks.normality i

def transition (i : Fin 16) (j : Fin 17) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow7NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow7NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow7NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow7NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow7NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow7NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalCertificate

end
