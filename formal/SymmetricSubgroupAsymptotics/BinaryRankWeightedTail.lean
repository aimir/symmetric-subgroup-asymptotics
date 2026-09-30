import SymmetricSubgroupAsymptotics.BinaryTargetOrderMoments

/-!
# Tilted tails of the binary character rank

For the complete source `J ≤ S_b` let `d₂(J)` be its binary character rank.
The same-source marker moment gives

`∑_{J ≤ S_b} 2^(q d₂(J)) ≤ s_{b+2q}`.

On the hot set `d₂(J) > a b`, for `0 ≤ ℓ ≤ q`, one has pointwise
`(q-ℓ) a b + ℓ d₂(J) ≤ q d₂(J)`.  Hence the tilted tail

`2^((q-ℓ) a b) ∑_{d₂(J) > a b} 2^(ℓ d₂(J)) ≤ s_{b+2q}`.

No graph injection beyond the existing marker moment and no literature
input is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The hot set of the binary rank at threshold `a`: `d₂(J) > a b`. -/
def BinaryRankHot (a : ℝ) {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) : Prop :=
  a * b < binaryCharacterRank J

/-- The complete weighted rank sum, in real form. -/
theorem binaryRankWeightedFullSum_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (2 : ℝ) ^ ((q : ℝ) * binaryCharacterRank J)) ≤
      (subgroupCount (b + 2 * q) : ℝ) := by
  have h := binaryTargetOrder_marker_moment_le 1 b q
  have hsum : (∑ J : Subgroup (Equiv.Perm (Fin b)),
      (2 : ℝ) ^ ((q : ℝ) * binaryCharacterRank J)) =
      ((∑ J : Subgroup (Equiv.Perm (Fin b)),
        (2 ^ (1 * binaryCharacterRank J)) ^ q : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [one_mul, ← pow_mul, mul_comm, ← Real.rpow_natCast]
    push_cast
    ring_nf
  rw [hsum, show b + 2 * q = b + q * (2 * 1) by ring]
  exact_mod_cast h

/-- The tilted hot tail: for `ℓ ≤ q`,
`2^((q-ℓ) a b) ∑_{d₂(J) > a b} 2^(ℓ d₂(J)) ≤ s_{b+2q}`. -/
theorem binaryRankWeightedHotSum_le (a : ℝ) (b q ℓ : ℕ) (hℓ : ℓ ≤ q) :
    (2 : ℝ) ^ (((q : ℝ) - ℓ) * a * b) *
        (∑ J ∈ Finset.univ.filter
            (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot a J),
          (2 : ℝ) ^ ((ℓ : ℝ) * binaryCharacterRank J)) ≤
      (subgroupCount (b + 2 * q) : ℝ) := by
  refine le_trans ?_ (binaryRankWeightedFullSum_le b q)
  rw [Finset.mul_sum]
  calc (∑ J ∈ Finset.univ.filter
          (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot a J),
        (2 : ℝ) ^ (((q : ℝ) - ℓ) * a * b) *
          (2 : ℝ) ^ ((ℓ : ℝ) * binaryCharacterRank J))
      ≤ ∑ J ∈ Finset.univ.filter
          (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot a J),
        (2 : ℝ) ^ ((q : ℝ) * binaryCharacterRank J) := by
        apply Finset.sum_le_sum
        intro J hJ
        have hhot : a * b < binaryCharacterRank J :=
          (Finset.mem_filter.mp hJ).2
        have hqℓ : (0 : ℝ) ≤ (q : ℝ) - ℓ := by
          have : (ℓ : ℝ) ≤ q := by exact_mod_cast hℓ
          linarith
        rw [← Real.rpow_add (by norm_num)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have := mul_le_mul_of_nonneg_left hhot.le hqℓ
        nlinarith
    _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
        (2 : ℝ) ^ ((q : ℝ) * binaryCharacterRank J) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)

/-- Division form of the tilted hot tail. -/
theorem binaryRankWeightedHotSum_le_div (a : ℝ) (b q ℓ : ℕ) (hℓ : ℓ ≤ q) :
    (∑ J ∈ Finset.univ.filter
          (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot a J),
        (2 : ℝ) ^ ((ℓ : ℝ) * binaryCharacterRank J)) ≤
      (2 : ℝ) ^ (-(((q : ℝ) - ℓ) * a * b)) * (subgroupCount (b + 2 * q) : ℝ) := by
  have h := binaryRankWeightedHotSum_le a b q ℓ hℓ
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (((q : ℝ) - ℓ) * a * b) := by positivity
  rw [Real.rpow_neg (by norm_num), ← div_eq_inv_mul, le_div_iff₀ hpos,
    mul_comm]
  exact h

/-- The untilted hot count (`ℓ = 0`):
`#{J ≤ S_b : d₂(J) > a b} ≤ 2^(-q a b) s_{b+2q}`. -/
theorem binaryRankHot_card_le (a : ℝ) (b q : ℕ) :
    ((Finset.univ.filter
        (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot a J)).card : ℝ) ≤
      (2 : ℝ) ^ (-((q : ℝ) * a * b)) * (subgroupCount (b + 2 * q) : ℝ) := by
  have h := binaryRankWeightedHotSum_le_div a b q 0 (Nat.zero_le q)
  simpa using h

end SymmetricSubgroupAsymptotics
