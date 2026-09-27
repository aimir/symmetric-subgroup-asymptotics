import SymmetricSubgroupAsymptotics.BinarySevenCharacterEnvelope
import SymmetricSubgroupAsymptotics.BinaryTransitiveCentralCriterion

/-!
# New character gaps from the actual central rank

The elementary comparison 5^3 < 2^7 proves the new exact criterion whenever
16*z ≤ 3*w. The actual central-rank bound for a nonregular faithful
transitive action supplies this at every power degree at least sixteen.
No conversion of an old 38/25 acceptance certificate is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem binarySeven_character_gap_of_sixteen_mul_le (w z : ℕ)
    (hw : 0<w) (hz : 16*z ≤ 3*w) :
    5^(16*z) < 2^(7*w) := by
  calc
    _ ≤ 5^(3*w) := Nat.pow_le_pow_right (by decide : 0<5) hz
    _ = (5^3)^w := by rw [pow_mul]
    _ < (2^7)^w := Nat.pow_lt_pow_left (by decide : (5:ℕ)^3<2^7) (by omega)
    _ = _ := by rw [pow_mul]

theorem sixteen_mul_pred_le_three_two_pow (k : ℕ) (hk : 4≤k) :
    16*(k-1) ≤ 3*2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      rw [Nat.succ_sub_one, pow_succ]
      omega

/-- Uniform symbolic gap, including the degree-sixteen endpoint. -/
theorem binarySeven_character_gap_power_degree (k z : ℕ)
    (hk : 4≤k) (hz : z<k) : 5^(16*z) < 2^(7*2^k) :=
  binarySeven_character_gap_of_sixteen_mul_le (2^k) z
    (pow_pos (by decide : 0<2) _)
    ((Nat.mul_le_mul_left 16 (by omega : z≤k-1)).trans
      (sixteen_mul_pred_le_three_two_pow k hk))

variable {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    [Finite X] [Nonempty X]

/-- The original faithful transitive action determines the central rank.
The group need not be binary for this algebraic criterion alone. -/
def binaryTransitivePower_sevenCharacterCriterion (k : ℕ) (hk : 4≤k)
    (hdegree : Nat.card X=2^k) (hlarge : 2^k<Nat.card G) :
    BinarySevenCharacterCriterion G (2^k) where
  dimension := Module.finrank (ZMod 2) (Additive (binaryCentralOmega G))
  cardinal := binaryCentralOmega_card_eq_pow_finrank
  gap := binarySeven_character_gap_power_degree k _ hk
    (binaryCentralOmega_finrank_lt_of_nonregular (G := G) (X := X) k hdegree
      (by simpa only [hdegree] using hlarge))

/-- The literal original bottom quotient is transported only by quotientBot. -/
def binaryTransitivePower_botSevenCharacterCriterion (k : ℕ) (hk : 4≤k)
    (U : Subgroup (Equiv.Perm (Fin (2^k))))
    [MulAction.IsPretransitive U (Fin (2^k))] (hlarge : 2^k<Nat.card U) :
    BinarySevenCharacterCriterion (U⧸(⊥:Subgroup U)) (2^k) :=
  (binaryTransitivePower_sevenCharacterCriterion (G := U) (X := Fin (2^k))
    k hk (Nat.card_fin _) hlarge).transport (QuotientGroup.quotientBot (G := U)).symm

end SymmetricSubgroupAsymptotics

end
