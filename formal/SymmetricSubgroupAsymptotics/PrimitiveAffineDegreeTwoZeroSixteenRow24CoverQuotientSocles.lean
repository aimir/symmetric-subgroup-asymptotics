import SymmetricSubgroupAsymptotics.FiniteNormalJoinCoverWordRegistry
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24ConjugacyCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalNormalityChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks

/-!
# Original zero16 row 24 quotients from the original-row cover

The normality and transition words are the retained original declarations.
Their fields are assembled directly with the selected original-row cover,
without using the old cardinal-cover registry object. The exact literal top
and every original normal quotient are retained throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow24CoverQuotientSocles

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Source := PrimitiveAffineSixteenFrameRow24TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow24TopCertificate.group

abbrev topAmbient := PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient
abbrev topRepresentative := PrimitiveAffineSixteenFrameRow24NormalCore.topRepresentative
abbrev stateGenerators := PrimitiveAffineSixteenFrameRow24NormalCore.stateGenerators
abbrev child := PrimitiveAffineSixteenFrameRow24NormalCore.child

theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow24NormalCore.topAmbient_full

def normality (i : Fin 8) :
    FiniteNormalityWordCertificate topAmbient (stateGenerators i) :=
  PrimitiveAffineSixteenFrameRow24NormalNormalityChecks.normality i

/-- Only the original parent, representative, and child word equations enter
this assembly. No old conjugacy-cardinality object is an argument. -/
def transition (i : Fin 8) (j : Fin 19) :
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (topRepresentative j)
      (stateGenerators (child i j)) where
  parentToChild := {
    words := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.parentWords i j
    equations := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.parentWords_checked i j }
  representativeWord := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.representativeWord i j
  representativeEquation := PrimitiveAffineSixteenFrameRow24NormalParentTransitionChecks.representativeWords_checked i j
  childWords := PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks.childWords i j
  childEquations := PrimitiveAffineSixteenFrameRow24NormalChildTransitionChecks.childWords_checked i j

private theorem bottom_eq :
    Subgroup.closure (Set.range (stateGenerators 0)) = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j <;> rfl
  · exact bot_le

/-- The existing generated fields now consume the actual original-row cover. -/
def data : FiniteNormalJoinCoverWordRegistryData
    PrimitiveAffineSixteenFrameRow24ConjugacyCover.cover topAmbient stateGenerators :=
  FiniteNormalJoinCoverWordRegistryData.ofFields
    PrimitiveAffineSixteenFrameRow24ConjugacyCover.cover
    topRepresentative
    PrimitiveAffineSixteenFrameRow24ConjugacyCover.representative_eq
    topAmbient stateGenerators topAmbient_full normality 0 bottom_eq child transition

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  data.complete N

private theorem two_steps (i : Fin 8) :
    ∃ a b : Fin 19,
      child (child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 6, rfl⟩
  · exact ⟨0, 9, rfl⟩
  · exact ⟨0, 11, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact data.normal_generating_pair two_steps N

/-- Equality of the ordered literal generators on the original points. -/
theorem generators_eq :
    PrimitiveAffineSixteenFrameRow24TopCertificate.generators =
      DegreeTwoZeroSixteenInterfaces.row24Generators := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

theorem top_eq :
    Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow24TopCertificate.generators) =
      DegreeTwoZeroSixteenInterfaces.row24.top := by
  change Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow24TopCertificate.generators) =
    Subgroup.closure (Set.range DegreeTwoZeroSixteenInterfaces.row24Generators)
  rw [generators_eq]

def originalEquiv : Source ≃* DegreeTwoZeroSixteenInterfaces.row24.top :=
  PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv.trans
    (MulEquiv.subgroupCongr top_eq)

theorem top_normal_generators
    (N : Subgroup DegreeTwoZeroSixteenInterfaces.row24.top) (hN : N.Normal) :
    ∃ x : Fin 2 → DegreeTwoZeroSixteenInterfaces.row24.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective source_normal_generators N hN

/-- The quotient is by the supplied original normal subgroup of the exact
literal row24 top. -/
theorem topSocle
    (N : {N : Subgroup DegreeTwoZeroSixteenInterfaces.row24.top // N.Normal}) :
    SocleNormalGeneratorBound (DegreeTwoZeroSixteenInterfaces.row24.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples top_normal_generators N.1

/-- Preserve the original interface's normal-state type and literal normals. -/
def family : DegreeTwoZeroSixteenInterfaces.row24.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    DegreeTwoZeroSixteenInterfaces.row24.normalRegistry topSocle

end PrimitiveAffineDegreeTwoZeroSixteenRow24CoverQuotientSocles
end SymmetricSubgroupAsymptotics

end
