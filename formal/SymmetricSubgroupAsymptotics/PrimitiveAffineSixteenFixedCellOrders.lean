import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenCompressedEightAction
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import Mathlib.Data.Fintype.Perm

/-! Fixed coefficient budgets for the actual two- and four-block affine16
translation cells. Only injectivity into the literal local wreath product
is used; correlated kernels are never replaced by the full product. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre=16)

include P hr in
theorem sixteen_complement_order_le : Nat.card (P.complement (origin block)) ≤ 2^15 := by
  have hh := Nat.card_le_card_of_injective
    (P.complementLinearMap_degreeSixteen block.component_preprimitive (origin block) hr)
    (P.complementLinearMap_degreeSixteen_injective block.component_preprimitive (origin block) hr)
  rw [GeneralFourTwoMatrixEncoding.ambient_card] at hh
  exact hh.trans (by norm_num)

include P hr in
theorem sixteen_component_order_le : Nat.card block.Component ≤ 2^19 := by
  have hfactor : Nat.card block.Component=16*Nat.card (P.complement (origin block)) := by
    simpa only [P.card_eq (origin block),hr] using
      (P.isComplement'_complement (origin block)).card_mul.symm
  rw [hfactor]
  exact (Nat.mul_le_mul_left 16 (sixteen_complement_order_le block P hr)).trans (by norm_num)

private theorem actual_top_order_le : Nat.card block.Top ≤ (Nat.card block.Points).factorial := by
  have hh := Nat.card_le_card_of_injective block.Top.subtype Subtype.val_injective
  have hc : Nat.card (Equiv.Perm block.Points)=(Nat.card block.Points).factorial := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm]
  exact hh.trans_eq hc

include P hr in
theorem sixteen_original_order_le :
    Nat.card (preE7NonPairAction w U) ≤
      2^(19*Nat.card block.Points)*(Nat.card block.Points).factorial := by
  have hh := Nat.card_le_card_of_injective
    (ambientEmbedding block) (ambientEmbedding_injective block)
  rw [PermutationalWreathProduct.natCard_eq] at hh
  apply hh.trans
  apply (Nat.mul_le_mul
    (Nat.pow_le_pow_left (sixteen_component_order_le block P hr) _)
    (actual_top_order_le block)).trans_eq
  rw [←pow_mul]

include P hr in
theorem sixteen_translation_quotient_order_le :
    Nat.card (preE7NonPairAction w U ⧸ E block P) ≤
      2^(15*Nat.card block.Points)*(Nat.card block.Points).factorial := by
  let e := MonoidHom.ofInjective (f := complementAction block P)
    (complementAction_injective block P)
  have hlocal : Nat.card (LocalQuotient block P) ≤ 2^15 :=
    (Nat.card_congr e.symm.toEquiv).trans_le (sixteen_complement_order_le block P hr)
  have hh := Nat.card_le_card_of_injective
    (quotientEmbedding block P) (quotientEmbedding_injective block P)
  rw [PermutationalWreathProduct.natCard_eq] at hh
  apply hh.trans
  apply (Nat.mul_le_mul (Nat.pow_le_pow_left hlocal _) (actual_top_order_le block)).trans_eq
  rw [←pow_mul]

include P hr in
theorem sixteen_twoBlock_order_budgets (hs : Nat.card block.Points=2) :
    Nat.card (preE7NonPairAction w U) ≤ 2^39 ∧
      Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2^31 := by
  constructor
  · simpa only [hs,Nat.reduceMul,Nat.factorial_two,←pow_succ] using
      sixteen_original_order_le block P hr
  · simpa only [hs,Nat.reduceMul,Nat.factorial_two,←pow_succ] using
      sixteen_translation_quotient_order_le block P hr

include P hr in
theorem sixteen_fourBlock_order_budgets (hs : Nat.card block.Points=4) :
    Nat.card (preE7NonPairAction w U) ≤ 2^81 ∧
      Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2^65 := by
  have hG := sixteen_original_order_le block P hr
  have hQ := sixteen_translation_quotient_order_le block P hr
  rw [hs] at hG hQ
  constructor
  · exact hG.trans (by norm_num)
  · exact hQ.trans (by norm_num)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
