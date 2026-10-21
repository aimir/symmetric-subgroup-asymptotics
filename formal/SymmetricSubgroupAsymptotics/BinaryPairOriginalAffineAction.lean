import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation

/-! Every actual original row has the literal triangular affine layer
action with its OWN retained offset. No zero-model premise is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w))
include E

theorem originalCoordinateRepresentation_actual_row (u : U) :
    E.originalCoordinateRepresentation u=
      pairLayerFlatten.toLinearMap.comp
        ((affinePairLayerMap (E.top u) (E.affineTranslation u)).comp
          pairLayerFlatten.symm.toLinearMap) := by
  apply LinearMap.ext
  intro v
  change E.originalCoordinateEquiv
    (fun x => (E.originalCoordinateEquiv.symm v) ((u : Equiv.Perm X)⁻¹ x))=_
  rw [←E.affinePermutation_original u]
  change pairLayerFlatten
      (E.pairLayerCoordinateEquiv
        (fun x => (E.originalCoordinateEquiv.symm v)
          ((E.affinePermutation (E.top u) (E.affineTranslation u))⁻¹ x)))=_
  rw [E.pairLayerCoordinateEquiv_affine_action]
  change pairLayerFlatten (affinePairLayerMap (E.top u) (E.affineTranslation u)
    (E.pairLayerCoordinateEquiv
      (E.pairLayerCoordinateEquiv.symm (pairLayerFlatten.symm v))))=_
  rw [E.pairLayerCoordinateEquiv.apply_symm_apply]
  rfl
end SymmetricSubgroupAsymptotics.BinaryPairFrame
