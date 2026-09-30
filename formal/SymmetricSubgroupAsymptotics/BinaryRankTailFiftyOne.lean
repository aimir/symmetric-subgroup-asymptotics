import SymmetricSubgroupAsymptotics.BinaryRankWeightedTail

/-!
# The rank-tail threshold `a = 51/200`

The excess `e = 1/200` over the quarter, `a = 1/4 + e = 51/200`, is shared
by SNS2, which keeps the weight `2^(ℓ d₂(J))`, and by the index-three kernel
tail of Y1, which uses `ℓ = 0`.  The tilt is `r = ⌈2 e b⌉ = ⌈b/100⌉`.  The
completed square is

`(b+2r)²/16 - (r-ℓ) a b = b²/16 - e² b² + ℓ a b + (r - 2 e b)²/4`,

so the deficit `b²/40000` survives up to `1/4`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The tilt `⌈b/100⌉` for the threshold `51/200`. -/
def rankTail51Tilt (b : ℕ) : ℕ := (b + 99) / 100

theorem rankTail51Tilt_bounds (b : ℕ) :
    (b : ℝ) ≤ 100 * rankTail51Tilt b ∧
      100 * (rankTail51Tilt b : ℝ) ≤ b + 99 := by
  have h1 : b ≤ 100 * rankTail51Tilt b := by
    unfold rankTail51Tilt
    omega
  have h2 : 100 * rankTail51Tilt b ≤ b + 99 := by
    unfold rankTail51Tilt
    omega
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The weighted square completion at `a = 51/200`, for every tilt `q` with
`b ≤ 100 q ≤ b + 99`:
`(b+2q)²/16 - (q-ℓ) a b ≤ b²/16 - b²/40000 + ℓ a b + 1/4`. -/
theorem rankTail51_squareCompletion_of_bounds (b ℓ : ℕ) (q : ℝ)
    (h1 : (b : ℝ) ≤ 100 * q) (h2 : 100 * q ≤ b + 99) :
    ((b : ℝ) + 2 * q) ^ 2 / 16 - (q - ℓ) * (51 / 200) * b ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 + (ℓ : ℝ) * (51 / 200) * b +
        1 / 4 := by
  have hd : 0 ≤ 100 * q - b := by linarith
  have hd' : 100 * q - b ≤ 99 := by linarith
  have hsq : (100 * q - b) * (100 * q - b) ≤ 99 * 99 :=
    mul_le_mul hd' hd' hd (by norm_num)
  nlinarith [hsq]

/-- The weighted square completion at the tilt `⌈b/100⌉`. -/
theorem rankTail51_squareCompletion (b ℓ : ℕ) :
    ((b : ℝ) + 2 * rankTail51Tilt b) ^ 2 / 16 -
        ((rankTail51Tilt b : ℝ) - ℓ) * (51 / 200) * b ≤
      (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 + (ℓ : ℝ) * (51 / 200) * b +
        1 / 4 :=
  rankTail51_squareCompletion_of_bounds b ℓ _ (rankTail51Tilt_bounds b).1
    (rankTail51Tilt_bounds b).2

/-- The weighted hot sum at `a = 51/200`, for any tilt `q ≥ ℓ`. -/
theorem binaryRankHot51_weightedSum_le (b q ℓ : ℕ) (hℓ : ℓ ≤ q) :
    (∑ J ∈ Finset.univ.filter
          (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot (51 / 200) J),
        (2 : ℝ) ^ ((ℓ : ℝ) * binaryCharacterRank J)) ≤
      (2 : ℝ) ^ (-(((q : ℝ) - ℓ) * (51 / 200) * b)) *
        (subgroupCount (b + 2 * q) : ℝ) :=
  binaryRankWeightedHotSum_le_div (51 / 200) b q ℓ hℓ

/-- The untilted hot count at `a = 51/200` and the tilt `⌈b/100⌉`. -/
theorem binaryRankHot51_card_le (b : ℕ) :
    ((Finset.univ.filter
        (fun J : Subgroup (Equiv.Perm (Fin b)) =>
          BinaryRankHot (51 / 200) J)).card : ℝ) ≤
      (2 : ℝ) ^ (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
        (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ) :=
  binaryRankHot_card_le (51 / 200) b (rankTail51Tilt b)

end SymmetricSubgroupAsymptotics
