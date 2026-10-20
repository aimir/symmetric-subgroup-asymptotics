import SymmetricSubgroupAsymptotics.FiniteNormalJoinCoverWordRegistry
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26ConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalChildTransitionChecks

/-!
# Original zero16 row 26 quotients from the original-row cover

The normality and transition words are the retained original declarations.
Their fields are assembled directly with the selected original-row cover,
without using the old cardinal-cover registry object. The exact literal top
and every original normal quotient are retained throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow26CoverQuotientSocles

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Source := PrimitiveAffineSixteenFrameRow26TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow26TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow26NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow26NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow26NormalCore.child

theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow26NormalCore.topAmbient_full

def normality (i : Fin 8) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow26NormalNormalityChecks.normality i

/-- Only the original parent, representative, and child word equations enter
this assembly. No old conjugacy-cardinality object is an argument. -/
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

/-- The existing generated fields now consume the actual original-row cover. -/
def data : FiniteNormalJoinCoverWordRegistryData
    PrimitiveAffineSixteenFrameRow26ConjugacyCover.cover topAmbient stateGenerators :=
  FiniteNormalJoinCoverWordRegistryData.ofFields
    PrimitiveAffineSixteenFrameRow26ConjugacyCover.cover
    topRepresentative
    PrimitiveAffineSixteenFrameRow26ConjugacyCover.representative_eq
    topAmbient stateGenerators topAmbient_full normality 0 bottom_eq child transition

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  data.complete N

private theorem two_steps (i : Fin 8) :
    ∃ a b : Fin 19,
      child (child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 6, rfl⟩
  · exact ⟨0, 9, rfl⟩
  · exact ⟨0, 11, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact data.normal_generating_pair two_steps N

/-- Equality of the ordered literal generators on the original points. -/
theorem generators_eq :
    PrimitiveAffineSixteenFrameRow26TopCertificate.generators =
      DegreeTwoZeroSixteenInterfaces.row26Generators := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

theorem top_eq :
    Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow26TopCertificate.generators) =
      DegreeTwoZeroSixteenInterfaces.row26.top := by
  change Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow26TopCertificate.generators) =
    Subgroup.closure (Set.range DegreeTwoZeroSixteenInterfaces.row26Generators)
  rw [generators_eq]

def originalEquiv : Source ≃* DegreeTwoZeroSixteenInterfaces.row26.top :=
  PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv.trans
    (MulEquiv.subgroupCongr top_eq)

theorem top_normal_generators
    (N : Subgroup DegreeTwoZeroSixteenInterfaces.row26.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoZeroSixteenInterfaces.row26.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective source_normal_generators N hN

/-- The quotient is by the supplied original normal subgroup of the exact
literal row26 top. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoZeroSixteenInterfaces.row26.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoZeroSixteenInterfaces.row26.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

/-- Preserve the original interface's normal-state type and literal normals. -/
def family : DegreeTwoZeroSixteenInterfaces.row26.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoZeroSixteenInterfaces.row26.normalRegistry topSocle

end PrimitiveAffineDegreeTwoZeroSixteenRow26CoverQuotientSocles
end SymmetricSubgroupAsymptotics

end
