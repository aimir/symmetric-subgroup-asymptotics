import SymmetricSubgroupAsymptotics.BinaryTransitiveCentralCriterion

/-!
# Exact character gaps for nonregular power-of-two actions

The original faithful transitive action bounds the dimension of its actual
central involution subgroup. At degree sixteen we retain the checked exact
integer comparison. At every larger power-of-two degree a uniform elementary
power inequality gives the same character criterion. This module supplies
only the algebraic criterion, not a character-count input or an aggregate
estimate over varying physical widths.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A convenient sufficient integer gap. The zero-dimensional case uses
the positive original width; positive dimensions use the strict `38 < 50`. -/
theorem binary_character_gap_of_eight_mul_le (w z : ℕ)
    (hw : 0 < w) (hz : 8*z ≤ w) :
    38^(8*z) < 2^w * 25^(8*z) := by
  by_cases hzero : z = 0
  · subst z
    simpa only [Nat.mul_zero, pow_zero, mul_one] using
      (Nat.pow_lt_pow_right (by decide : 1 < 2) hw)
  · calc
      38^(8*z) < 50^(8*z) :=
        Nat.pow_lt_pow_left (by decide : 38 < 50) (by omega : 8*z ≠ 0)
      _ = 2^(8*z) * 25^(8*z) := by
        rw [show (50 : ℕ) = 2*25 from rfl, mul_pow]
      _ ≤ 2^w * 25^(8*z) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 2) hz)

/-- Beyond degree sixteen the dimension bound `z < k` leaves enough room
for the elementary sufficient gap at width `2^k`. -/
theorem eight_mul_pred_le_two_pow (k : ℕ) (hk : 5 ≤ k) :
    8*(k-1) ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      rw [Nat.succ_sub_one, pow_succ]
      omega

/-- Exact integer character gap for every power-of-two width at least
sixteen and every dimension strictly smaller than its logarithmic degree. -/
theorem binary_character_gap_power_degree (k z : ℕ)
    (hk : 4 ≤ k) (hz : z < k) :
    38^(8*z) < 2^(2^k) * 25^(8*z) := by
  by_cases hfour : k = 4
  · subst k
    exact binary_character_gap_sixteen_of_le_three z (by omega)
  · apply binary_character_gap_of_eight_mul_le (2^k) z
      (pow_pos (by decide : 0 < 2) k)
    exact (Nat.mul_le_mul_left 8 (by omega : z ≤ k-1)).trans
      (eight_mul_pred_le_two_pow k (by omega))

variable {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    [Finite X] [Nonempty X]

/-- The criterion concerns the actual group and its given faithful
transitive action. Neither binary structure nor a quotient action is
assumed to derive this finite algebraic statement. -/
def binaryTransitivePower_characterCriterion (k : ℕ) (hk : 4 ≤ k)
    (hdegree : Nat.card X = 2^k) (hlarge : 2^k < Nat.card G) :
    BinaryNormalCharacterCriterion G (2^k) where
  dimension := Module.finrank (ZMod 2) (Additive (binaryCentralOmega G))
  cardinal := binaryCentralOmega_card_eq_pow_finrank
  gap := binary_character_gap_power_degree k _ hk
    (binaryCentralOmega_finrank_lt_of_nonregular (G := G) (X := X) k hdegree
      (by simpa only [hdegree] using hlarge))

/-- The literal bottom quotient of the original permutation subgroup.
Only `quotientBot` transports the criterion; the original points are kept. -/
def binaryTransitivePower_botCharacterCriterion (k : ℕ) (hk : 4 ≤ k)
    (U : Subgroup (Equiv.Perm (Fin (2^k))))
    [MulAction.IsPretransitive U (Fin (2^k))] (hlarge : 2^k < Nat.card U) :
    BinaryNormalCharacterCriterion (U ⧸ (⊥ : Subgroup U)) (2^k) :=
  (binaryTransitivePower_characterCriterion (G := U) (X := Fin (2^k))
    k hk (Nat.card_fin (2^k)) hlarge).transport
      (QuotientGroup.quotientBot (G := U)).symm

end SymmetricSubgroupAsymptotics

end
