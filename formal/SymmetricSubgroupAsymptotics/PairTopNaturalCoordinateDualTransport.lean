import SymmetricSubgroupAsymptotics.BinaryPairActualKernelDualSections
import SymmetricSubgroupAsymptotics.RepresentationDualComp
import SymmetricSubgroupAsymptotics.SurjectiveRepresentationGeneratorTransport

/-! Actual top and point-coordinate transport for the natural binary module.
The permutation relation is explicit, so an abstract group equivalence alone
never substitutes a different permutation action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PairTopNaturalCoordinateDualTransport

variable {I L : Type} [Fintype I] [Fintype L]
    (P : Subgroup (Equiv.Perm I)) (T : Subgroup (Equiv.Perm L))
    (e : P ≃* T) (coords : I ≃ L)
    (hact : ∀ (p : P) (i : I), coords ((p : Equiv.Perm I) i)=
      (e p : Equiv.Perm L) (coords i))

def reindex : Representation.IntertwiningMap
    (permutationFunctionRepresentation (ZMod 2) P I)
    ((permutationFunctionRepresentation (ZMod 2) T L).comp e.toMonoidHom) where
  toLinearMap := {
    toFun := fun v x => v (coords.symm x)
    map_add' := by intro _ _; rfl
    map_smul' := by intro _ _; rfl }
  isIntertwining' p := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((p : Equiv.Perm I)⁻¹ (coords.symm x))=
      v (coords.symm ((e p : Equiv.Perm L)⁻¹ x))
    have hx : coords ((p : Equiv.Perm I)⁻¹ (coords.symm x))=
        (e p : Equiv.Perm L)⁻¹ x := by
      simpa only [map_inv, Subgroup.coe_inv, Equiv.apply_symm_apply] using
        hact p⁻¹ (coords.symm x)
    simpa only [Equiv.symm_apply_apply] using
      congrArg (fun y : L => v (coords.symm y)) hx

theorem reindex_injective : Function.Injective (reindex P T e coords hact) := by
  intro v w h
  funext i
  have hi := congrFun h (coords i)
  change v (coords.symm (coords i))=w (coords.symm (coords i)) at hi
  simpa only [Equiv.symm_apply_apply] using hi

include e coords hact in
theorem dual_uniform {H : ℕ}
    (hdual : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T L).dual H) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) P I).dual H := by
  have hp : UniformSubrepresentationGeneratorBound
      (Representation.dual ((permutationFunctionRepresentation (ZMod 2) T L).comp
        e.toMonoidHom)) H := by
    rw [representation_dual_comp]
    exact hdual.comp_of_surjective _ e.toMonoidHom e.surjective
  exact hp.of_surjective (RepresentationHeadExact.dualMap (reindex P T e coords hact))
    (LinearMap.dualMap_surjective_of_injective (reindex_injective P T e coords hact))

end SymmetricSubgroupAsymptotics.PairTopNaturalCoordinateDualTransport
