import SymmetricSubgroupAsymptotics.FiniteNormalJoinCoverWordRegistry
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27ConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalChildTransitionChecks

/-!
# Original zero16 row 27 quotients from the original-row cover

The normality and transition words are the retained original declarations.
Their fields are assembled directly with the selected original-row cover,
without using the old cardinal-cover registry object. The exact literal top
and every original normal quotient are retained throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow27CoverQuotientSocles

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Source := PrimitiveAffineSixteenFrameRow27TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow27TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow27NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow27NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow27NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow27NormalCore.child

theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow27NormalCore.topAmbient_full

def normality (i : Fin 22) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow27NormalNormalityChecks.normality i

/-- Only the original parent, representative, and child word equations enter
this assembly. No old conjugacy-cardinality object is an argument. -/
def transition (i : Fin 22) (j : Fin 33) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow27NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow27NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow27NormalChildTransitionChecks.childWords_checked i j

private theorem bottom_eq :
    Subgroup.closure (Set.range (stateGenerators 0)) = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> rfl
  · exact bot_le

/-- The existing generated fields now consume the actual original-row cover. -/
def data : FiniteNormalJoinCoverWordRegistryData
    PrimitiveAffineSixteenFrameRow27ConjugacyCover.cover topAmbient stateGenerators :=
  FiniteNormalJoinCoverWordRegistryData.ofFields
    PrimitiveAffineSixteenFrameRow27ConjugacyCover.cover
    topRepresentative
    PrimitiveAffineSixteenFrameRow27ConjugacyCover.representative_eq
    topAmbient stateGenerators topAmbient_full normality 0 bottom_eq child transition

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  data.complete N

private theorem two_steps (i : Fin 22) :
    ∃ a b : Fin 33,
      child (child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨0, 13, rfl⟩
  · exact ⟨0, 20, rfl⟩
  · exact ⟨0, 5, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨0, 17, rfl⟩
  · exact ⟨0, 15, rfl⟩
  · exact ⟨0, 23, rfl⟩
  · exact ⟨0, 24, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 12, rfl⟩
  · exact ⟨0, 19, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 16, rfl⟩
  · exact ⟨0, 22, rfl⟩
  · exact ⟨0, 6, rfl⟩
  · exact ⟨0, 18, rfl⟩
  · exact ⟨0, 28, rfl⟩
  · exact ⟨0, 26, rfl⟩
  · exact ⟨0, 7, rfl⟩
  · exact ⟨7, 19, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact data.normal_generating_pair two_steps N

/-- Equality of the ordered literal generators on the original points. -/
theorem generators_eq :
    PrimitiveAffineSixteenFrameRow27TopCertificate.generators =
      DegreeTwoZeroSixteenInterfaces.row27Generators := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

theorem top_eq :
    Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow27TopCertificate.generators) =
      DegreeTwoZeroSixteenInterfaces.row27.top := by
  change Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow27TopCertificate.generators) =
    Subgroup.closure (Set.range DegreeTwoZeroSixteenInterfaces.row27Generators)
  rw [generators_eq]

def originalEquiv : Source ≃* DegreeTwoZeroSixteenInterfaces.row27.top :=
  PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv.trans
    (MulEquiv.subgroupCongr top_eq)

theorem top_normal_generators
    (N : Subgroup DegreeTwoZeroSixteenInterfaces.row27.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoZeroSixteenInterfaces.row27.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective source_normal_generators N hN

/-- The quotient is by the supplied original normal subgroup of the exact
literal row27 top. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoZeroSixteenInterfaces.row27.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoZeroSixteenInterfaces.row27.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

/-- Preserve the original interface's normal-state type and literal normals. -/
def family : DegreeTwoZeroSixteenInterfaces.row27.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoZeroSixteenInterfaces.row27.normalRegistry topSocle

end PrimitiveAffineDegreeTwoZeroSixteenRow27CoverQuotientSocles
end SymmetricSubgroupAsymptotics

end
