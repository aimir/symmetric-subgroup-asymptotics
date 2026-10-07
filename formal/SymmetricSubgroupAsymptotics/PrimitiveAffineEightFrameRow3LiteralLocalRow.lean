import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrderTwelveLocalCatalogue

/-!
# Selected eight-frame row 21: literal local row

This wrapper identifies the executable three-element subgroup in the row-3
certificate with the stabilizer of point zero in its literal degree-eight
permutation action.  Thus the stored local epimorphism is an exact map on
the literal point stabilizer, rather than an order-only label.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3LiteralLocalRow

open PrimitiveAffineEightFrameRow3InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow3TopCertificate.group

local instance inStabilizerDecidable (i : Fin 96) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

local instance sourceStabilizerMembership (s : Source) :
    Decidable (s ∈ sourceStabilizer) :=
  inStabilizerDecidable s.index

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow3TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv_apply]
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv.map_mul s.1 t.1

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow3InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow3InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inl PrimitiveAffineEightFrameRow3InducedBinding.localTarget_card

theorem literalStabilizer_card :
    Nat.card (MulAction.stabilizer LiteralAction (0 : Fin 8)) = 12 := by
  rw [Nat.card_congr sourceStabilizerEquivLiteral.toEquiv.symm]
  exact PrimitiveAffineEightFrameRow3InducedBinding.sourceStabilizer_card

private theorem source_center_eq_bot :
    Subgroup.center sourceStabilizer = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    revert x
    native_decide
  · exact bot_le

theorem literal_center_eq_bot :
    Subgroup.center (MulAction.stabilizer LiteralAction (0 : Fin 8)) = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hs : sourceStabilizerEquivLiteral.symm x ∈
        Subgroup.center sourceStabilizer :=
      MulEquivClass.apply_mem_center sourceStabilizerEquivLiteral.symm hx
    have hsone : sourceStabilizerEquivLiteral.symm x = 1 := by
      simpa only [source_center_eq_bot, Subgroup.mem_bot] using hs
    rw [Subgroup.mem_bot]
    calc
      x = sourceStabilizerEquivLiteral
          (sourceStabilizerEquivLiteral.symm x) := by simp
      _ = 1 := by rw [hsone]; simp
  · exact bot_le

noncomputable def literalLocalCatalogue :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue LiteralAction :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue.singletonOfOrderTwelveCyclicThree
    LiteralAction literalLocalRow literalStabilizer_card
    PrimitiveAffineEightFrameRow3InducedBinding.localTarget_card
    literal_center_eq_bot

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3LiteralLocalRow

end
