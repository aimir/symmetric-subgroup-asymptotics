import SymmetricSubgroupAsymptotics.FiniteNormalJoinCoverWordRegistry
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25ConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalChildTransitionChecks

/-!
# Original zero16 row 25 quotients from the original-row cover

The normality and transition words are the retained original declarations.
Their fields are assembled directly with the selected original-row cover,
without using the old cardinal-cover registry object. The exact literal top
and every original normal quotient are retained throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow25CoverQuotientSocles

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Source := PrimitiveAffineSixteenFrameRow25TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow25TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow25NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow25NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow25NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow25NormalCore.child

theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow25NormalCore.topAmbient_full

def normality (i : Fin 14) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow25NormalNormalityChecks.normality i

/-- Only the original parent, representative, and child word equations enter
this assembly. No old conjugacy-cardinality object is an argument. -/
def transition (i : Fin 14) (j : Fin 24) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow25NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow25NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow25NormalChildTransitionChecks.childWords_checked i j

private theorem bottom_eq :
    Subgroup.closure (Set.range (stateGenerators 0)) = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> rfl
  · exact bot_le

/-- The existing generated fields now consume the actual original-row cover. -/
def data : FiniteNormalJoinCoverWordRegistryData
    PrimitiveAffineSixteenFrameRow25ConjugacyCover.cover topAmbient stateGenerators :=
  FiniteNormalJoinCoverWordRegistryData.ofFields
    PrimitiveAffineSixteenFrameRow25ConjugacyCover.cover
    topRepresentative
    PrimitiveAffineSixteenFrameRow25ConjugacyCover.representative_eq
    topAmbient stateGenerators topAmbient_full normality 0 bottom_eq child transition

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  data.complete N

private theorem two_steps (i : Fin 14) :
    ∃ a b : Fin 24,
      child (child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨0, 8, rfl⟩
  · exact ⟨0, 6, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨0, 10, rfl⟩
  · exact ⟨0, 12, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 9, rfl⟩
  · exact ⟨0, 11, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 7, rfl⟩
  · exact ⟨0, 13, rfl⟩
  · exact ⟨0, 14, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact data.normal_generating_pair two_steps N

/-- Equality of the ordered literal generators on the original points. -/
theorem generators_eq :
    PrimitiveAffineSixteenFrameRow25TopCertificate.generators =
      DegreeTwoZeroSixteenInterfaces.row25Generators := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

theorem top_eq :
    Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow25TopCertificate.generators) =
      DegreeTwoZeroSixteenInterfaces.row25.top := by
  change Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow25TopCertificate.generators) =
    Subgroup.closure (Set.range DegreeTwoZeroSixteenInterfaces.row25Generators)
  rw [generators_eq]

def originalEquiv : Source ≃* DegreeTwoZeroSixteenInterfaces.row25.top :=
  PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv.trans
    (MulEquiv.subgroupCongr top_eq)

theorem top_normal_generators
    (N : Subgroup DegreeTwoZeroSixteenInterfaces.row25.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoZeroSixteenInterfaces.row25.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective source_normal_generators N hN

/-- The quotient is by the supplied original normal subgroup of the exact
literal row25 top. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoZeroSixteenInterfaces.row25.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoZeroSixteenInterfaces.row25.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

/-- Preserve the original interface's normal-state type and literal normals. -/
def family : DegreeTwoZeroSixteenInterfaces.row25.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoZeroSixteenInterfaces.row25.normalRegistry topSocle

end PrimitiveAffineDegreeTwoZeroSixteenRow25CoverQuotientSocles
end SymmetricSubgroupAsymptotics

end
