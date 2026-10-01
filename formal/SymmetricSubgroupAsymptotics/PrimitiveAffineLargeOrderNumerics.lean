import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure

/-!
# The large-degree affine order cutoff

The affine point stabilizer embeds in the automorphism group of the regular
elementary-abelian subgroup.  This file proves the remaining elementary
numerical fact behind the SO cutoff: from degree `1024` onward the resulting
catalogue-free order bound is at most `2^(w/8)`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The elementary exponential domination used at the affine cutoff. -/
theorem eight_mul_succ_sq_le_two_pow {l : ℕ} (hl : 10 ≤ l) :
    8 * (l + 1) ^ 2 ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      rw [pow_succ]
      calc
        8 * (l + 1 + 1) ^ 2 ≤ 2 * (8 * (l + 1) ^ 2) := by nlinarith
        _ ≤ 2 * 2 ^ l := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (l + 1) := by rw [pow_succ]; omega

/-- For `w ≥ 1024`, the universal affine order expression lies below the
SO threshold. -/
theorem domain_pow_log_le_two_pow_eighth {w : ℕ} (hw : 1024 ≤ w) :
    w * w ^ Nat.log 2 w ≤ 2 ^ (w / 8) := by
  let l := Nat.log 2 w
  have hw0 : w ≠ 0 := by omega
  have hl10 : 10 ≤ l := by
    dsimp [l]
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    norm_num
    exact hw
  have hpowLower : 2 ^ l ≤ w := by
    exact Nat.pow_log_le_self 2 hw0
  have hsquareMul : 8 * (l + 1) ^ 2 ≤ w :=
    (eight_mul_succ_sq_le_two_pow hl10).trans hpowLower
  have hsquare : (l + 1) ^ 2 ≤ w / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
    simpa [Nat.mul_comm] using hsquareMul
  have hwUpper : w ≤ 2 ^ (l + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) w).le
  calc
    w * w ^ Nat.log 2 w = w ^ (l + 1) := by
      dsimp [l]
      rw [pow_succ']
    _ ≤ (2 ^ (l + 1)) ^ (l + 1) := Nat.pow_le_pow_left hwUpper _
    _ = 2 ^ ((l + 1) ^ 2) := by rw [pow_two, pow_mul]
    _ ≤ 2 ^ (w / 8) := Nat.pow_le_pow_right (by norm_num) hsquare

/-- The fourth-power menu exponent is still only linear in the degree from
the same cutoff onward. -/
theorem succ_sq_sq_add_succ_sq_le_sixteen_pow {l : ℕ} (hl : 10 ≤ l) :
    ((l + 1) ^ 2) ^ 2 + (l + 1) ^ 2 ≤ 16 * 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      calc
        ((l + 1 + 1) ^ 2) ^ 2 + (l + 1 + 1) ^ 2 ≤
            2 * (((l + 1) ^ 2) ^ 2 + (l + 1) ^ 2) := by nlinarith
        _ ≤ 2 * (16 * 2 ^ l) := Nat.mul_le_mul_left 2 ih
        _ = 16 * 2 ^ (l + 1) := by rw [pow_succ]; ring

namespace PrimitiveAffineProfile

variable {L : Type} [Group L] {w : ℕ} [MulAction L (Fin w)]
  (P : PrimitiveAffineProfile L (Fin w))

include P

/-- Every faithful primitive affine action of degree at least `1024` has the
small exponential order required by the SO owner. -/
theorem card_le_two_pow_eighth [Finite L] [FaithfulSMul L (Fin w)]
    (hw : 1024 ≤ w) (x : Fin w) : Nat.card L ≤ 2 ^ (w / 8) := by
  calc
    Nat.card L ≤ Nat.card (Fin w) *
        Nat.card (Fin w) ^ Nat.log 2 (Nat.card (Fin w)) :=
      card_le_domain_pow_log P x
    _ = w * w ^ Nat.log 2 w := by simp
    _ ≤ 2 ^ (w / 8) := domain_pow_log_le_two_pow_eighth hw

/-- The sharper logarithmic-square order ceiling used as the SO parameter. -/
theorem card_le_two_pow_logSquare [Finite L] [FaithfulSMul L (Fin w)]
    (x : Fin w) :
    Nat.card L ≤ 2 ^ ((Nat.log 2 w + 1) ^ 2) := by
  let l := Nat.log 2 w
  have hwUpper : w ≤ 2 ^ (l + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) w).le
  calc
    Nat.card L ≤ Nat.card (Fin w) *
        Nat.card (Fin w) ^ Nat.log 2 (Nat.card (Fin w)) :=
      card_le_domain_pow_log P x
    _ = w ^ (l + 1) := by simp [l, pow_succ']
    _ ≤ (2 ^ (l + 1)) ^ (l + 1) := Nat.pow_le_pow_left hwUpper _
    _ = 2 ^ ((Nat.log 2 w + 1) ^ 2) := by
      dsimp [l]
      rw [pow_two, pow_mul]

/-- The logarithmic-square parameter meets the SO margin at width `1024`. -/
theorem eight_mul_logSquare_le [Finite L] [FaithfulSMul L (Fin w)]
    (hw : 1024 ≤ w) : 8 * ((Nat.log 2 w + 1) ^ 2) ≤ w := by
  have hw0 : w ≠ 0 := by omega
  have hl10 : 10 ≤ Nat.log 2 w := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    norm_num
    exact hw
  exact (eight_mul_succ_sq_le_two_pow hl10).trans
    (Nat.pow_log_le_self 2 hw0)

end PrimitiveAffineProfile

end SymmetricSubgroupAsymptotics

end
