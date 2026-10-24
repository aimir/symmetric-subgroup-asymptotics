import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOuterBound
import SymmetricSubgroupAsymptotics.ReeGTwoRectangularClassNumerics

/-! Actual original ReeG2 order bounds from the same fixed group's
proved two-cell cardinality and its actual derived subgroup. No
perfectness of the full fixed group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOrderBounds
open CFSGReeGTwoFixedModelEquivalence CFSGReeGTwoFixedCardinalitySylow
open CFSGReeGTwoDerivedCenter PrimitiveSocleRawStructure ReeGTwoRectangularClassNumerics
attribute [local instance] fixedModel_finite

theorem original_order_le_seventh (m : ℕ) (hm : 1 ≤ m) :
    Nat.card (CFSG.Models.ReeG2 m) ≤ (3^(2*m+1))^7 := by
  rw [Nat.card_congr (originalReeEquivDerived m hm).toEquiv]
  have hc := (commutator (originalModelFixed m)).card_le_card_group
  rw [fixed_group_card] at hc
  exact hc.trans (order_le_seventh _ (Nat.one_le_pow _ _ (by decide)))

theorem original_component_le_eighth (m : ℕ) (hm : 1 ≤ m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] :
    Nat.card (CFSG.Models.ReeG2 m)*Nat.card (Outer (CFSG.Models.ReeG2 m)) ≤
      (3^(2*m+1))^8 := by
  have hout := (CFSGReeGTwoOriginalOuterBound.outer_card_le m hm).trans
    (twice_le_three_pow (2*m+1))
  exact (Nat.mul_le_mul (original_order_le_seventh m hm) hout).trans_eq (by ring)

theorem original_order_ge_1024 (m : ℕ) (hm : 1 ≤ m) :
    1024 ≤ Nat.card (CFSG.Models.ReeG2 m) := by
  have hq : 27 ≤ 3^(2*m+1) :=
    Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (by omega : 3 ≤ 2*m+1)
  have hq3 := Nat.pow_le_pow_left hq 3
  have hc := Nat.mul_le_mul
    (Nat.mul_le_mul hq3 (by omega : 26 ≤ 3^(2*m+1)-1))
    (Nat.add_le_add_right hq3 1)
  have hb := hc.trans (CFSGReeGTwoDerivedIndex.original_order_lower m hm)
  omega

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOrderBounds
