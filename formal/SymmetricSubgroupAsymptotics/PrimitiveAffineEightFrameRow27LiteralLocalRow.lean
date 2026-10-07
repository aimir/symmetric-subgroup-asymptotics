import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue

/-!
# Selected eight-frame row 27: literal local row

This wrapper identifies the executable three-element subgroup in the row-27
certificate with the stabilizer of point zero in its literal degree-eight
permutation action.  Thus the stored local epimorphism is an exact map on
the literal point stabilizer, rather than an order-only label.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27LiteralLocalRow

open PrimitiveAffineEightFrameRow27InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow27TopCertificate.group

local instance inStabilizerDecidable (i : Fin 168) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow27TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv_apply]
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow27TopCertificate.originalEquiv.map_mul s.1 t.1

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow27InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow27InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow27InducedBinding.localTarget_card

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27LiteralLocalRow

end
