import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFramePointedTopMatch

/-!
# Kernel-checked local-row dispatcher for an eight-point top

The thirty frame rows are not a list of thirty top groups: several rows
share a top and differ by the normal kernel of an onto map from a point
stabilizer to `C3` or `S3`.  This interface states the exact completeness
property needed after a literal top has been selected.

Keeping the interface per literal top makes the four ineligible top classes
harmless.  Their row type is empty, and completeness proves that no onto
local map of order three or six exists for them.  No numerical kernel-order
lookup appears in the consumer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- One literal stabilizer quotient row for a fixed eight-point top. -/
structure DegreeEightLiteralLocalRow
    (T : Subgroup (Equiv.Perm (Fin 8))) : Type 1 where
  ModelLocalGroup : Type
  [modelLocalGroup : Group ModelLocalGroup]
  [modelLocalFinite : Finite ModelLocalGroup]
  literalLocalMap : MulAction.stabilizer T (0 : Fin 8) →* ModelLocalGroup
  literalLocalMap_surjective : Function.Surjective literalLocalMap
  local_card : Nat.card ModelLocalGroup = 3 ∨
    Nat.card ModelLocalGroup = 6

attribute [instance]
  DegreeEightLiteralLocalRow.modelLocalGroup
  DegreeEightLiteralLocalRow.modelLocalFinite

namespace DegreeEightLiteralLocalRow

/-- A checked normal kernel in the literal point stabilizer supplies the
local row directly through its canonical quotient.  The eight-frame
emitter therefore need not build a second Cayley group or certify a
separate multiplication table for its order-three/order-six images. -/
noncomputable def ofNormalKernel
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup (MulAction.stabilizer T (0 : Fin 8))) [N.Normal]
    (hcard : Nat.card
      (MulAction.stabilizer T (0 : Fin 8) ⧸ N) = 3 ∨
      Nat.card (MulAction.stabilizer T (0 : Fin 8) ⧸ N) = 6) :
    DegreeEightLiteralLocalRow T where
  ModelLocalGroup := MulAction.stabilizer T (0 : Fin 8) ⧸ N
  literalLocalMap := QuotientGroup.mk' N
  literalLocalMap_surjective := QuotientGroup.mk'_surjective N
  local_card := hcard

/-- Cardinality form specialized to the selected order-21 stabilizer and
its recorded order-seven kernel. -/
noncomputable def ofOrderSevenKernelInOrderTwentyOne
    (T : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup (MulAction.stabilizer T (0 : Fin 8))) [N.Normal]
    (hsource : Nat.card (MulAction.stabilizer T (0 : Fin 8)) = 21)
    (hkernel : Nat.card N = 7) :
    DegreeEightLiteralLocalRow T := by
  apply DegreeEightLiteralLocalRow.ofNormalKernel T N
  left
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hsource, hkernel] at hmul
  omega

end DegreeEightLiteralLocalRow

/-- Complete, kernel-checked dispatcher for all eligible stabilizer
quotients of one literal top.  `complete` asks for equality of the maps
after an explicit target equivalence.  It therefore classifies kernels and
images simultaneously. -/
structure DegreeEightLiteralLocalRowCatalogue
    (T : Subgroup (Equiv.Perm (Fin 8))) : Type 1 where
  Row : Type
  row : Row → DegreeEightLiteralLocalRow T
  complete :
    ∀ (L : Type) [Group L] [Finite L]
      (f : MulAction.stabilizer T (0 : Fin 8) →* L),
      Function.Surjective f →
      (Nat.card L = 3 ∨ Nat.card L = 6) →
      ∃ r : Row, ∃ e : L ≃* (row r).ModelLocalGroup,
        e.toMonoidHom.comp f = (row r).literalLocalMap

namespace DegreeEightLiteralLocalRowCatalogue

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Apply a literal top's complete local-row dispatcher to the actual
zero-core local map.  The chosen actual point is the preimage of row point
zero, so no pointed-conjugacy hypothesis is required. -/
noncomputable def selectActual
    {ModelGroup : Type} [Group ModelGroup]
    (topMatch : DegreeFourZeroCoreEightLiteralTopMatch
      block ModelGroup)
    (C : DegreeEightLiteralLocalRowCatalogue topMatch.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    C.Row ×
      DegreeFourZeroCoreEightPointedLocalMatch
        block P topMatch hr hD (0 : Fin 8) := by
  let f := DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap
    (block := block) (P := P) topMatch hr hD (0 : Fin 8)
  let hselected := C.complete (LocalQuotient block P) f
    (DegreeFourZeroCoreEightLiteralTopMatch.transportedLocalMap_surjective
      (block := block) (P := P) topMatch hr hD (0 : Fin 8))
    (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
  let r : C.Row := Classical.choose hselected
  let e : LocalQuotient block P ≃* (C.row r).ModelLocalGroup :=
    Classical.choose (Classical.choose_spec hselected)
  have he : e.toMonoidHom.comp f = (C.row r).literalLocalMap :=
    Classical.choose_spec (Classical.choose_spec hselected)
  exact ⟨r, {
    ModelLocalGroup := (C.row r).ModelLocalGroup
    literalLocalMap := (C.row r).literalLocalMap
    literalLocalMap_surjective := (C.row r).literalLocalMap_surjective
    targetEquiv := e
    compatible := he }⟩

end DegreeEightLiteralLocalRowCatalogue

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
