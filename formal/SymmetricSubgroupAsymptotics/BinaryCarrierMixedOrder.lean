import SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions

/-! Original group-order bounds in physical carrier weight. Every P
occurrence contributes one extra binary exponent: its order is128 while
its physical scale is1. The sharp cap6T+#P implies the uniform cap7T.
Original occurrences and physical scales are never changed by this count.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions

open BinaryCarrierWord BinaryCarrierMixedMenuWord

/-- One extra binary order exponent for each literal P occurrence. -/
def pOccurrence : Kind → ℕ
  | .p => 1
  | _ => 0

theorem pOccurrence_le_scale (k : Kind) : pOccurrence k ≤ factorScaleNat k := by
  cases k <;> simp [pOccurrence, factorScaleNat]

/-- X and J have order64, P has order128, and each degree-sixteen master
has order at most4096. The physical scale of P remains one. -/
theorem factor_card_le_order (k : Kind) :
    Nat.card (factor k).Carrier ≤ 2^(6*factorScaleNat k+pOccurrence k) := by
  cases k with
  | x =>
      change Nat.card BinaryCarrierNormalRows8T26.Original ≤ 2^(6*1+0)
      exact BinaryMenuCayley8T26.exact_card.le
  | j =>
      change Nat.card BinaryCarrierNormalRows8T27.Original ≤ 2^(6*1+0)
      exact BinaryMenuCayley8T27.exact_card.le
  | p =>
      change Nat.card BinaryCarrierNormalRows8T35.Original ≤ 2^(6*1+1)
      exact BinaryMenuCayley8T35.exact_card.le
  | degree16 m => exact BinaryCarrierMasterWords16.factor_card_le m

/-- Uniform order exponent per physical unit for all eight literal masters. -/
theorem factor_card_le_scale (k : Kind) :
    Nat.card (factor k).Carrier ≤ 2^(7*factorScaleNat k) := by
  apply (factor_card_le_order k).trans
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have h := pOccurrence_le_scale k
  omega

def wordScale : List Kind → ℕ
  | [] => 0
  | k :: kinds => factorScaleNat k + wordScale kinds

/-- Repeated P factors each contribute once, independently of normal labels. -/
def pCount : List Kind → ℕ
  | [] => 0
  | k :: kinds => pOccurrence k + pCount kinds

theorem pCount_le_wordScale (kinds : List Kind) : pCount kinds ≤ wordScale kinds := by
  induction kinds with
  | nil => exact Nat.le_refl 0
  | cons k kinds ih => exact Nat.add_le_add (pOccurrence_le_scale k) ih

theorem wordScale_cast (kinds : List Kind) : (wordScale kinds : ℝ) = totalScale kinds := by
  induction kinds with
  | nil => simp only [wordScale, totalScale, Nat.cast_zero]
  | cons k kinds ih =>
      simp only [wordScale, totalScale, Nat.cast_add, factorScaleNat_cast, ih]

/-- The sharper original product order retains the actual number of P factors. -/
theorem product_card_le_order (kinds : List Kind) :
    Nat.card (Product (word kinds)) ≤ 2^(6*wordScale kinds+pCount kinds) := by
  induction kinds with
  | nil => change Nat.card PUnit ≤ 2^(6*0+0); simp
  | cons k kinds ih =>
      change Nat.card ((factor k).Carrier × Product (word kinds)) ≤
        2^(6*(factorScaleNat k+wordScale kinds)+(pOccurrence k+pCount kinds))
      rw [Nat.card_prod]
      calc
        _ ≤ 2^(6*factorScaleNat k+pOccurrence k) *
            2^(6*wordScale kinds+pCount kinds) :=
          Nat.mul_le_mul (factor_card_le_order k) ih
        _ = _ := by
          rw [← pow_add]
          congr 1
          ring

/-- A uniform cap for every original product, without excluding P. -/
theorem product_card_le_scale (kinds : List Kind) :
    Nat.card (Product (word kinds)) ≤ 2^(7*wordScale kinds) := by
  apply (product_card_le_order kinds).trans
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have h := pCount_le_wordScale kinds
  omega

theorem subgroup_card_le_order (kinds : List Kind) (H : Subgroup (Product (word kinds))) :
    Nat.card H ≤ 2^(6*wordScale kinds+pCount kinds) :=
  (Nat.card_le_card_of_injective H.subtype H.subtype_injective).trans
    (product_card_le_order kinds)

/-- An actual subgroup of the original product has the same uniform cap. -/
theorem subgroup_card_le_scale (kinds : List Kind) (H : Subgroup (Product (word kinds))) :
    Nat.card H ≤ 2^(7*wordScale kinds) :=
  (Nat.card_le_card_of_injective H.subtype H.subtype_injective).trans
    (product_card_le_scale kinds)

/-- The former exponent6T is retained whenever the actual P count is zero. -/
theorem product_card_le_scale_of_pCount_eq_zero (kinds : List Kind) (h : pCount kinds = 0) :
    Nat.card (Product (word kinds)) ≤ 2^(6*wordScale kinds) := by
  simpa only [h, Nat.add_zero] using product_card_le_order kinds

theorem subgroup_card_le_scale_of_pCount_eq_zero (kinds : List Kind)
    (H : Subgroup (Product (word kinds))) (h : pCount kinds = 0) :
    Nat.card H ≤ 2^(6*wordScale kinds) := by
  simpa only [h, Nat.add_zero] using subgroup_card_le_order kinds H

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions
