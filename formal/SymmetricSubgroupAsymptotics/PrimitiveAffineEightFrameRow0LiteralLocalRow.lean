import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue

/-!
# Selected eight-frame row 0: literal local row

This wrapper identifies the executable three-element subgroup in the row-0
certificate with the stabilizer of point zero in its literal degree-eight
permutation action.  Thus the stored local epimorphism is an exact map on
the literal point stabilizer, rather than an order-only label.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0LiteralLocalRow

open PrimitiveAffineEightFrameRow0InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow0TopCertificate.group

local instance inStabilizerDecidable (i : Fin 24) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv_apply]
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.map_mul s.1 t.1

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow0InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow0InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow0InducedBinding.localTarget_card

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0LiteralLocalRow

end
