import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFramePointedTopMatch
import SymmetricSubgroupAsymptotics.FaithfulBinaryPlaneOrderSixNoncommutative
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport

/-!
# Kernel-checked local-row dispatcher for an sixteen-point top

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

/-- One literal stabilizer quotient row for a fixed sixteen-point top. -/
structure DegreeSixteenLiteralLocalRow
    (T : Subgroup (Equiv.Perm (Fin 16))) : Type 1 where
  ModelLocalGroup : Type
  [modelLocalGroup : Group ModelLocalGroup]
  [modelLocalFinite : Finite ModelLocalGroup]
  literalLocalMap : MulAction.stabilizer T (0 : Fin 16) →* ModelLocalGroup
  literalLocalMap_surjective : Function.Surjective literalLocalMap
  local_card : Nat.card ModelLocalGroup = 3 ∨
    Nat.card ModelLocalGroup = 6

attribute [instance]
  DegreeSixteenLiteralLocalRow.modelLocalGroup
  DegreeSixteenLiteralLocalRow.modelLocalFinite

namespace DegreeSixteenLiteralLocalRow

/-- A checked normal kernel in the literal point stabilizer supplies the
local row directly through its canonical quotient.  The sixteen-frame
emitter therefore need not build a second Cayley group or certify a
separate multiplication table for its order-three/order-six images. -/
noncomputable def ofNormalKernel
    (T : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup (MulAction.stabilizer T (0 : Fin 16))) [N.Normal]
    (hcard : Nat.card
      (MulAction.stabilizer T (0 : Fin 16) ⧸ N) = 3 ∨
      Nat.card (MulAction.stabilizer T (0 : Fin 16) ⧸ N) = 6) :
    DegreeSixteenLiteralLocalRow T where
  ModelLocalGroup := MulAction.stabilizer T (0 : Fin 16) ⧸ N
  literalLocalMap := QuotientGroup.mk' N
  literalLocalMap_surjective := QuotientGroup.mk'_surjective N
  local_card := hcard

/-- Cardinality form specialized to the selected order-21 stabilizer and
its recorded order-seven kernel. -/
noncomputable def ofOrderSevenKernelInOrderTwentyOne
    (T : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup (MulAction.stabilizer T (0 : Fin 16))) [N.Normal]
    (hsource : Nat.card (MulAction.stabilizer T (0 : Fin 16)) = 21)
    (hkernel : Nat.card N = 7) :
    DegreeSixteenLiteralLocalRow T := by
  apply DegreeSixteenLiteralLocalRow.ofNormalKernel T N
  left
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hsource, hkernel] at hmul
  omega

end DegreeSixteenLiteralLocalRow

/-- Complete, kernel-checked dispatcher for all eligible stabilizer
quotients of one literal top.  `complete` asks for equality of the maps
after an explicit target equivalence.  It therefore classifies kernels and
images simultaneously. -/
structure DegreeSixteenLiteralLocalRowCatalogue
    (T : Subgroup (Equiv.Perm (Fin 16))) : Type 1 where
  Row : Type
  row : Row → DegreeSixteenLiteralLocalRow T
  complete :
    ∀ (L : Type) [Group L] [Finite L]
      (f : MulAction.stabilizer T (0 : Fin 16) →* L),
      Function.Surjective f →
      (Nat.card L = 3 ∨
        (Nat.card L = 6 ∧ ¬ IsMulCommutative L)) →
      ∃ r : Row, ∃ e : L ≃* (row r).ModelLocalGroup,
        e.toMonoidHom.comp f = (row r).literalLocalMap

namespace DegreeSixteenLiteralLocalRowCatalogue

/-- If the literal point stabilizer itself has order three, every eligible
local quotient is the displayed order-three row. -/
noncomputable def singletonOfSourceOrderThree
    (T : Subgroup (Equiv.Perm (Fin 16)))
    (R : DegreeSixteenLiteralLocalRow T)
    (hsource : Nat.card (MulAction.stabilizer T (0 : Fin 16)) = 3)
    (htarget : Nat.card R.ModelLocalGroup = 3) :
    DegreeSixteenLiteralLocalRowCatalogue T where
  Row := Unit
  row _ := R
  complete := by
    intro L _ _ f hf hcard
    rcases hcard with hL | ⟨hL, _⟩
    · have hfker : Nat.card f.ker = 1 := by
        have hmul := f.ker.card_mul_index
        rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
          Nat.card_congr Subgroup.topEquiv.toEquiv, hsource, hL] at hmul
        omega
      have hRker : Nat.card R.literalLocalMap.ker = 1 := by
        have hmul := R.literalLocalMap.ker.card_mul_index
        rw [Subgroup.index_ker,
          R.literalLocalMap.range_eq_top_of_surjective
            R.literalLocalMap_surjective,
          Nat.card_congr Subgroup.topEquiv.toEquiv,
          hsource, htarget] at hmul
        omega
      have hkernels : f.ker = R.literalLocalMap.ker := by
        rw [(Subgroup.card_eq_one).mp hfker,
          (Subgroup.card_eq_one).mp hRker]
      refine ⟨(), surjectiveTargetEquivOfKernelEq f R.literalLocalMap
        hf R.literalLocalMap_surjective hkernels, ?_⟩
      exact surjectiveTargetEquivOfKernelEq_comp f R.literalLocalMap
        hf R.literalLocalMap_surjective hkernels
    · have hdvd : 6 ∣ 3 := by
        rw [← hL, ← hsource]
        exact Subgroup.card_dvd_of_surjective f hf
      norm_num at hdvd

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- A selected local row with the target identification retained in its
type.  This is the dependent form needed by a shared-top table: after the
catalogue chooses a row, the induced-module certificate for precisely that
row can be used without an external label or a cast between unrelated
finite target types. -/
structure ActualMatch
    {ModelGroup : Type} [Group ModelGroup]
    (topMatch : DegreeFourZeroCoreSixteenLiteralTopMatch block ModelGroup)
    (R : DegreeSixteenLiteralLocalRow topMatch.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) : Type where
  targetEquiv : LocalQuotient block P ≃* R.ModelLocalGroup
  compatible : targetEquiv.toMonoidHom.comp
      (DegreeFourZeroCoreSixteenLiteralTopMatch.transportedLocalMap
        (block := block) (P := P) topMatch hr hD (0 : Fin 16)) =
    R.literalLocalMap

namespace ActualMatch

/-- Forget only the row index after turning an exact match into the pointed
local comparison consumed by the induced-frame transport. -/
noncomputable def toPointedLocalMatch
    {ModelGroup : Type} [Group ModelGroup]
    {topMatch : DegreeFourZeroCoreSixteenLiteralTopMatch block ModelGroup}
    {R : DegreeSixteenLiteralLocalRow topMatch.literalAction}
    {hr : Nat.card block.Fibre = 4}
    {hD : degreeFourTernaryCore block P = ⊥}
    (M : ActualMatch block P topMatch R hr hD) :
    DegreeFourZeroCoreSixteenPointedLocalMatch
      block P topMatch hr hD (0 : Fin 16) where
  ModelLocalGroup := R.ModelLocalGroup
  literalLocalMap := R.literalLocalMap
  literalLocalMap_surjective := R.literalLocalMap_surjective
  local_card := R.local_card
  targetEquiv := M.targetEquiv
  compatible := M.compatible

end ActualMatch

/-- Apply a literal top's complete local-row dispatcher to the actual
zero-core local map.  The chosen actual point is the preimage of row point
zero, so no pointed-conjugacy hypothesis is required. -/
noncomputable def selectActual
    {ModelGroup : Type} [Group ModelGroup]
    (topMatch : DegreeFourZeroCoreSixteenLiteralTopMatch
      block ModelGroup)
    (C : DegreeSixteenLiteralLocalRowCatalogue topMatch.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    C.Row ×
      DegreeFourZeroCoreSixteenPointedLocalMatch
        block P topMatch hr hD (0 : Fin 16) := by
  let f := DegreeFourZeroCoreSixteenLiteralTopMatch.transportedLocalMap
    (block := block) (P := P) topMatch hr hD (0 : Fin 16)
  let hselected := C.complete (LocalQuotient block P) f
    (DegreeFourZeroCoreSixteenLiteralTopMatch.transportedLocalMap_surjective
      (block := block) (P := P) topMatch hr hD (0 : Fin 16))
    (by
      rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with
        h3 | h6
      · exact Or.inl h3
      · refine Or.inr ⟨h6, ?_⟩
        let C0 := chart block P
        letI : Fact P.p.Prime := C0.primeFact
        have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
        have hV : Module.finrank (ZMod P.p) C0.V = 2 := by
          change C0.d = 2
          exact (degreeFour_translationDimension block P hr).2
        exact not_isMulCommutative_of_faithful_binary_plane_card_six_at
          hp (binaryAffineLocalLinearRepresentation block P).ρ h6 hV
          (binaryAffineLocalLinearRepresentation_injective block P))
  let r : C.Row := Classical.choose hselected
  let e : LocalQuotient block P ≃* (C.row r).ModelLocalGroup :=
    Classical.choose (Classical.choose_spec hselected)
  have he : e.toMonoidHom.comp f = (C.row r).literalLocalMap :=
    Classical.choose_spec (Classical.choose_spec hselected)
  exact ⟨r, {
    ModelLocalGroup := (C.row r).ModelLocalGroup
    literalLocalMap := (C.row r).literalLocalMap
    literalLocalMap_surjective := (C.row r).literalLocalMap_surjective
    local_card := (C.row r).local_card
    targetEquiv := e
    compatible := he }⟩

/-- Apply a literal top's complete dispatcher while retaining the selected
row in the type of its comparison witness.  This is the canonical selection
API for grouped finite-frame catalogues. -/
noncomputable def selectActualExact
    {ModelGroup : Type} [Group ModelGroup]
    (topMatch : DegreeFourZeroCoreSixteenLiteralTopMatch
      block ModelGroup)
    (C : DegreeSixteenLiteralLocalRowCatalogue topMatch.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    Σ r : C.Row, ActualMatch block P topMatch (C.row r) hr hD := by
  let f := DegreeFourZeroCoreSixteenLiteralTopMatch.transportedLocalMap
    (block := block) (P := P) topMatch hr hD (0 : Fin 16)
  let hselected := C.complete (LocalQuotient block P) f
    (DegreeFourZeroCoreSixteenLiteralTopMatch.transportedLocalMap_surjective
      (block := block) (P := P) topMatch hr hD (0 : Fin 16))
    (by
      rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with
        h3 | h6
      · exact Or.inl h3
      · refine Or.inr ⟨h6, ?_⟩
        let C0 := chart block P
        letI : Fact P.p.Prime := C0.primeFact
        have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
        have hV : Module.finrank (ZMod P.p) C0.V = 2 := by
          change C0.d = 2
          exact (degreeFour_translationDimension block P hr).2
        exact not_isMulCommutative_of_faithful_binary_plane_card_six_at
          hp (binaryAffineLocalLinearRepresentation block P).ρ h6 hV
          (binaryAffineLocalLinearRepresentation_injective block P))
  let r : C.Row := Classical.choose hselected
  let e : LocalQuotient block P ≃* (C.row r).ModelLocalGroup :=
    Classical.choose (Classical.choose_spec hselected)
  have he : e.toMonoidHom.comp f = (C.row r).literalLocalMap :=
    Classical.choose_spec (Classical.choose_spec hselected)
  exact ⟨r, e, he⟩

end DegreeSixteenLiteralLocalRowCatalogue

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
