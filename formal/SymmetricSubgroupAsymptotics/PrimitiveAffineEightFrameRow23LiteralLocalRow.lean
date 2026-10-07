import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameOrderSixLocalCatalogue
import SymmetricSubgroupAsymptotics.FaithfulBinaryPlaneOrderSixNoncommutative

/-!
# Selected eight-frame row 23: exact literal local catalogue

The executable point stabilizer and its faithful binary-plane image both have
order six.  The reusable faithful-plane theorem makes that image
noncommutative, which rules out an order-three quotient and makes the stored
row the complete eligible local catalogue.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23LiteralLocalRow

open PrimitiveAffineEightFrameRow23InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow23TopCertificate.group

local instance inStabilizerDecidable (i : Fin 48) :
    Decidable (inStabilizer i) := by
  unfold inStabilizer
  infer_instance

local instance sourceStabilizerMembership (s : Source) :
    Decidable (s ∈ sourceStabilizer) :=
  inStabilizerDecidable s.index

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineEightFrameRow23TopCertificate.generators)

private theorem inStabilizer_iff_fixes_zero : ∀ s : Source,
    inStabilizer s.index ↔
      ((((PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv s :
        LiteralAction) : Equiv.Perm (Fin 8))) (0 : Fin 8) = 0) := by
  simp only [PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv_apply]
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃*
      MulAction.stabilizer LiteralAction (0 : Fin 8) where
  toFun s := ⟨PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv s.1,
    (inStabilizer_iff_fixes_zero s.1).mp s.2⟩
  invFun t :=
    ⟨PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.symm t.1,
      (inStabilizer_iff_fixes_zero
        (PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.symm t.1)).mpr
        (by
          rw [PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.apply_symm_apply]
          exact t.2)⟩
  left_inv s := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.symm_apply_apply s.1
  right_inv t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.apply_symm_apply t.1
  map_mul' s t := by
    apply Subtype.ext
    exact PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.map_mul s.1 t.1

def literalLocalMap :
    MulAction.stabilizer LiteralAction (0 : Fin 8) →*
      PrimitiveAffineEightFrameRow23InducedBinding.LocalTarget :=
  sourceLocalMap.comp sourceStabilizerEquivLiteral.symm.toMonoidHom

theorem literalLocalMap_surjective : Function.Surjective literalLocalMap :=
  sourceLocalMap_surjective.comp sourceStabilizerEquivLiteral.symm.surjective

noncomputable def literalLocalRow :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRow LiteralAction where
  ModelLocalGroup := PrimitiveAffineEightFrameRow23InducedBinding.LocalTarget
  literalLocalMap := literalLocalMap
  literalLocalMap_surjective := literalLocalMap_surjective
  local_card := Or.inr PrimitiveAffineEightFrameRow23InducedBinding.localTarget_card

theorem literalStabilizer_card :
    Nat.card (MulAction.stabilizer LiteralAction (0 : Fin 8)) = 6 := by
  rw [Nat.card_congr sourceStabilizerEquivLiteral.toEquiv.symm]
  exact PrimitiveAffineEightFrameRow23InducedBinding.sourceStabilizer_card

theorem localTarget_noncommutative :
    ¬ IsMulCommutative
      PrimitiveAffineEightFrameRow23InducedBinding.LocalTarget :=
  not_isMulCommutative_of_faithful_binary_plane_card_six
    PrimitiveAffineEightFrameRow23InducedBinding.localRepresentation
    PrimitiveAffineEightFrameRow23InducedBinding.localTarget_card
    (by simp)
    PrimitiveAffineEightFrameRow23InducedBinding.localRepresentation_injective

noncomputable def literalLocalCatalogue :
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue LiteralAction :=
  _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightLiteralLocalRowCatalogue.singletonOfNoncommutativeOrderSix
    LiteralAction literalLocalRow literalStabilizer_card
    PrimitiveAffineEightFrameRow23InducedBinding.localTarget_card
    localTarget_noncommutative

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23LiteralLocalRow

end
