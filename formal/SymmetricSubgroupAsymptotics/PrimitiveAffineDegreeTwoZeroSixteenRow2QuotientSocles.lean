import SymmetricSubgroupAsymptotics.FiniteNormalJoinTwoGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalCertificate

/-!
# Quotient socles for the literal zero-sixteen row two

The degree-four frame certificate uses exactly this row's three literal
permutations. Its four normal states are reached from bottom by two
class-representative transitions. The existing normal-word certificate
therefore supplies two normal generators for every normal subgroup, and
hence for every quotient socle of the original degree-two top.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow2QuotientSocles

abbrev Source := PrimitiveAffineSixteenFrameRow2TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineSixteenFrameRow2TopCertificate.group

/-- Equality of the ordered generator tuples on the original sixteen points. -/
theorem generators_eq :
    PrimitiveAffineSixteenFrameRow2TopCertificate.generators =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2Generators := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

/-- The reused top is literally the existing degree-two interface's top. -/
theorem top_eq :
    Subgroup.closure
        (Set.range PrimitiveAffineSixteenFrameRow2TopCertificate.generators) =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top := by
  change Subgroup.closure
      (Set.range PrimitiveAffineSixteenFrameRow2TopCertificate.generators) =
    Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2Generators)
  rw [generators_eq]

/-- Retain the original action when transporting the checked finite source. -/
noncomputable def originalEquiv : Source ≃* Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top :=
  PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv.trans
    (MulEquiv.subgroupCongr top_eq)

/-- Only the four existing transition-index rows are reduced here. -/
private theorem two_steps (i : Fin 4) :
    ∃ a b : Fin 8,
      PrimitiveAffineSixteenFrameRow2NormalCertificate.child
        (PrimitiveAffineSixteenFrameRow2NormalCertificate.child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨0, 1, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact PrimitiveAffineSixteenFrameRow2NormalCertificate.data.toRegistry.normal_generating_pair
    two_steps N

theorem top_normal_generators
    (N : Subgroup Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top) (hN : N.Normal) :
    ∃ x : Fin 2 → Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective
    source_normal_generators N hN

/-- Every actual normal quotient of the existing literal top has a
two-position socle normal-generating tuple. -/
theorem topSocle (N : {N : Subgroup Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top // N.Normal}) :
    SocleNormalGeneratorBound (Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

/-- Supply the original interface's canonical normal registry without
changing its state type or any of its literal normal subgroups. -/
noncomputable def family :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row2.normalRegistry topSocle

end PrimitiveAffineDegreeTwoZeroSixteenRow2QuotientSocles
end SymmetricSubgroupAsymptotics

end
