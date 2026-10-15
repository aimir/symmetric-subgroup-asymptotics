import SymmetricSubgroupAsymptotics.FiniteNormalJoinTwoGenerators
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenInterfaces
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalCertificate

/-!
# Selected literal sixteen-point quotient-socle adapter

Prepared using `emit_existing_registry_two_generators.py` for ZeroSixteen
row 22, degree-four owner 22. Every normal state is reached by two
existing class-representative transitions. No group, socle, or vector
enumeration is used. This output still requires a bounded Lean check.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRow22QuotientSocles

abbrev Source := PrimitiveAffineSixteenFrameRow22TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow22TopCertificate.group

/-- Equality of the ordered literal generators on the original points. -/
theorem generators_eq :
    PrimitiveAffineSixteenFrameRow22TopCertificate.generators = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22Generators := by
  funext j
  apply Equiv.ext
  intro x
  fin_cases j <;> fin_cases x <;> rfl

theorem top_eq :
    Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow22TopCertificate.generators) =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.top := by
  change Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow22TopCertificate.generators) =
    Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22Generators)
  rw [generators_eq]

noncomputable def originalEquiv : Source ≃* Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.top :=
  PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv.trans (MulEquiv.subgroupCongr top_eq)

private theorem two_steps (i : Fin 13) :
    ∃ a b : Fin 16,
      PrimitiveAffineSixteenFrameRow22NormalCertificate.child (PrimitiveAffineSixteenFrameRow22NormalCertificate.child 0 a) b = i := by
  fin_cases i
  · exact ⟨0, 0, rfl⟩
  · exact ⟨0, 9, rfl⟩
  · exact ⟨0, 2, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨0, 13, rfl⟩
  · exact ⟨0, 11, rfl⟩
  · exact ⟨0, 12, rfl⟩
  · exact ⟨0, 6, rfl⟩
  · exact ⟨0, 7, rfl⟩
  · exact ⟨0, 3, rfl⟩
  · exact ⟨0, 5, rfl⟩
  · exact ⟨0, 4, rfl⟩
  · exact ⟨1, 3, rfl⟩

theorem source_normal_generators (N : Subgroup Source) (hN : N.Normal) :
    ∃ x : Fin 2 → Source, Subgroup.normalClosure (Set.range x) = N := by
  letI := hN
  exact PrimitiveAffineSixteenFrameRow22NormalCertificate.data.toRegistry.normal_generating_pair two_steps N

theorem top_normal_generators (N : Subgroup Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.top) (hN : N.Normal) :
    ∃ x : Fin 2 → Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.top,
      Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective
    originalEquiv.toMonoidHom originalEquiv.surjective source_normal_generators N hN

theorem topSocle (N : {N : Subgroup Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.top // N.Normal}) :
    SocleNormalGeneratorBound (Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.top ⧸ N.1) 2 := by
  letI := N.2
  exact quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    top_normal_generators N.1

/-- Keep the original interface's normal-state type and literal subgroups. -/
noncomputable def family :
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  Non2UnipotentPrefixFiniteMenu.FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoZeroSixteenInterfaces.row22.normalRegistry topSocle

end PrimitiveAffineDegreeTwoZeroSixteenRow22QuotientSocles
end SymmetricSubgroupAsymptotics

end
