import SymmetricSubgroupAsymptotics.FiniteNormalJoinTwoGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalCertificate

/-!
# Selected literal sixteen-point quotient-socle adapter

Prepared from the existing checked adapter pattern for ZeroSixteen
row 5, degree-four owner 5. Every normal state is reached by two
existing class-representative transitions. No group, socle, or vector
enumeration is used. This output still requires a bounded Lean check.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow5QuotientSocles

abbrev Source := PrimitiveAffineSixteenFrameRow5TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

/-- Equality of the ordered literal generators on the original points. -/
theorem generators_eq :
    PrimitiveAffineSixteenFrameRow5TopCertificate.generators = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5Generators := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

theorem top_eq :
    Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow5TopCertificate.generators) =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.top := by
  change Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow5TopCertificate.generators) =
    Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5Generators)
  rw [generators_eq]

noncomputable def originalEquiv : Source ≃* Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.top :=
  PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv.trans (MulEquiv.subgroupCongr top_eq)

private theorem two_steps (i : Fin 7) :
    ∃ a b : Fin 10,
      PrimitiveAffineSixteenFrameRow5NormalCertificate.child (PrimitiveAffineSixteenFrameRow5NormalCertificate.child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 6, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 8, rfl⟩
  · exact ⟨0, 7, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 2, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact PrimitiveAffineSixteenFrameRow5NormalCertificate.data.toRegistry.normal_generating_pair two_steps N

theorem top_normal_generators (N : Subgroup Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.top) (hN : N.Normal) :
    ∃ x : Fin 2 → Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective source_normal_generators N hN

theorem topSocle (N : {N : Subgroup Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.top // N.Normal}) :
    SocleNormalGeneratorBound (Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

/-- Keep the original interface's normal-state type and literal subgroups. -/
noncomputable def family :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row5.normalRegistry topSocle

end PrimitiveAffineDegreeTwoZeroSixteenRow5QuotientSocles
end SymmetricSubgroupAsymptotics

end
