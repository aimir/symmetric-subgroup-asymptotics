import SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions

/-! Original group-order bounds in physical carrier weight. These bounds
refer to every literal occurrence, including repetitions, and supply the
order parameter used by the separate Hall-mixture estimate.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions

open BinaryCarrierWord BinaryCarrierMixedMenuWord

/-- The current J/five-master menu satisfies even the stronger exponent
six per unit of physical carrier weight. -/
theorem factor_card_le_scale (k : Kind) :
    Nat.card (factor k).Carrier ≤ 2^(6*factorScaleNat k) := by
  cases k with
  | j =>
      change Nat.card BinaryCarrierNormalRows8T27.Original ≤ 2^(6*1)
      exact BinaryMenuCayley8T27.exact_card.le
  | degree16 m => exact BinaryCarrierMasterWords16.factor_card_le m

def wordScale : List Kind → ℕ
  | [] => 0
  | k :: kinds => factorScaleNat k + wordScale kinds

theorem wordScale_cast (kinds : List Kind) : (wordScale kinds : ℝ) = totalScale kinds := by
  induction kinds with
  | nil => simp only [wordScale, totalScale, Nat.cast_zero]
  | cons k kinds ih =>
      simp only [wordScale, totalScale, Nat.cast_add, factorScaleNat_cast, ih]

/-- This bounds the original product order, not the size of a row menu. -/
theorem product_card_le_scale (kinds : List Kind) :
    Nat.card (Product (word kinds)) ≤ 2^(6*wordScale kinds) := by
  induction kinds with
  | nil => change Nat.card PUnit ≤ 2^(6*0); simp
  | cons k kinds ih =>
      change Nat.card ((factor k).Carrier × Product (word kinds)) ≤
        2^(6*(factorScaleNat k+wordScale kinds))
      rw [Nat.card_prod, Nat.mul_add, pow_add]
      exact Nat.mul_le_mul (factor_card_le_scale k) ih

/-- An actual subgroup of the original product has the same order cap. -/
theorem subgroup_card_le_scale (kinds : List Kind) (H : Subgroup (Product (word kinds))) :
    Nat.card H ≤ 2^(6*wordScale kinds) :=
  (Nat.card_le_card_of_injective H.subtype H.subtype_injective).trans
    (product_card_le_scale kinds)

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions
