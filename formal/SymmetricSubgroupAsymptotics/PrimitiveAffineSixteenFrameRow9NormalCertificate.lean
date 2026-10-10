import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalChildTransitionChecks


/-! Assembled checked normal registry.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalCertificate

abbrev Source := PrimitiveAffineSixteenFrameRow9NormalCore.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow9TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow9NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow9NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow9NormalCore.child
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow9NormalCore.topAmbient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow9NormalCore.topConjugacy

def normality (i : Fin 17) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow9NormalNormalityChecks.normality i

def transition (i : Fin 17) (j : Fin 18) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow9NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow9NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow9NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow9NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow9NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow9NormalChildTransitionChecks.childWords_checked i j

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

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalCertificate

end
