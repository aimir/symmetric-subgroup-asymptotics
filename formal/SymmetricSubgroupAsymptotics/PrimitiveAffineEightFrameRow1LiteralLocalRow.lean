import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue

/-!
# Selected eight-frame row 1: literal local row

This wrapper identifies the executable three-element subgroup in the row-1
certificate with the stabilizer of point zero in its literal degree-eight
permutation action.  Thus the stored local epimorphism is an exact map on
the literal point stabilizer, rather than an order-only label.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1LiteralLocalRow

open PrimitiveAffineEightFrameRow1InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow1TopCertificate.group

local instance inStabilizerDecidable (i : Fin 24) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow1TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv_apply]
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.map_mul s.1 t.1

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow1InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow1InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow1InducedBinding.localTarget_card

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1LiteralLocalRow

end
