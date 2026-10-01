import SymmetricSubgroupAsymptotics.MarkedC4PeelRecurrence
import SymmetricSubgroupAsymptotics.MarkedC4AsymptoticTransfer

/-!
# The bounded-word recurrence with an explicit error

This is the numerical endpoint of the RDT Case-I/Case-II decomposition.  Once
the structural decomposition supplies the normalized recurrence below, its
finite error is `O(b log(b+r+2))`; no asymptotic estimate remains inside the
bounded-word induction.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- A normalized bounded-word recurrence.  `count b r` is dominated by
`2^F(b,r)` times `normalized b r`.  Case I and all Case-II peels give the
single recurrence with polynomial error base `(b+r+2)^A`. -/
structure BoundedWordNormalizedRecurrence (count : ℕ → ℕ → ℝ) where
  A : ℝ
  A_nonneg : 0 ≤ A
  normalized : ℕ → ℕ → ℝ
  zero : ∀ r, normalized 0 r ≤ 1
  recurrence : ∀ b r, 0 < b →
    normalized b r ≤ ((b : ℝ) + r + 2) ^ A *
      (1 + ∑ k ∈ Finset.range b, normalized k r)
  denormalize : ∀ b r, count b r ≤
    (2 : ℝ) ^ markedF b r * normalized b r

namespace BoundedWordNormalizedRecurrence

variable {count : ℕ → ℕ → ℝ}
  (D : BoundedWordNormalizedRecurrence count)

/-- Closed finite bound produced by the normalized peel recurrence. -/
theorem normalized_le (b r : ℕ) :
    D.normalized b r ≤
      ((((b : ℝ) + r + 2) ^ D.A) * (b + 1)) ^ b := by
  let E : ℕ → ℝ := fun n => ((n : ℝ) + r + 2) ^ D.A
  have hE : ∀ n, 1 ≤ E n := by
    intro n
    apply Real.one_le_rpow
    · dsimp [E]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
    · exact D.A_nonneg
  have hEmono : Monotone E := by
    intro m n hmn
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast (show m + r + 2 ≤ n + r + 2 by omega)
    · exact D.A_nonneg
  have hrec : ∀ n, 0 < n →
      D.normalized n r ≤ E n *
        (1 + ∑ k ∈ Finset.range n, D.normalized k r) := by
    intro n hn
    exact D.recurrence n r hn
  simpa only [E] using
    (normalized_peel_recurrence_le (fun n => D.normalized n r) E
      (D.zero r) hE hEmono hrec b)

/-- The bounded-word recurrence has the required marked quadratic plus an
explicit `b log(b+r+2)` error. -/
theorem count_le_explicit (b r : ℕ) :
    count b r ≤
      (2 : ℝ) ^
        (markedF b r +
          ((D.A + 1) / Real.log 2) * b *
            Real.log ((b : ℝ) + r + 2)) := by
  let X : ℝ := (b : ℝ) + r + 2
  have hX : 0 < X := by positivity
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hX1 : 1 ≤ X := by dsimp [X]; linarith
  have hb1 : ((b : ℝ) + 1) ≤ X := by
    dsimp [X]
    linarith
  have hfactor : X ^ D.A * ((b : ℝ) + 1) ≤ X ^ (D.A + 1) := by
    calc
      X ^ D.A * ((b : ℝ) + 1) ≤ X ^ D.A * X :=
        mul_le_mul_of_nonneg_left hb1 (Real.rpow_nonneg hX.le _)
      _ = X ^ (D.A + 1) := by
        rw [Real.rpow_add hX]
        simp
  have hnorm := D.normalized_le b r
  have hfactorPow : (X ^ D.A * ((b : ℝ) + 1)) ^ b ≤
      (X ^ (D.A + 1)) ^ b :=
    pow_le_pow_left₀ (by positivity) hfactor b
  have hdenorm := D.denormalize b r
  calc
    count b r ≤ (2 : ℝ) ^ markedF b r * D.normalized b r := hdenorm
    _ ≤ (2 : ℝ) ^ markedF b r *
        (X ^ D.A * ((b : ℝ) + 1)) ^ b := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [X] using hnorm
      · positivity
    _ ≤ (2 : ℝ) ^ markedF b r * (X ^ (D.A + 1)) ^ b :=
      mul_le_mul_of_nonneg_left hfactorPow (by positivity)
    _ = (2 : ℝ) ^
        (markedF b r + ((D.A + 1) / Real.log 2) * b * Real.log X) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le,
        Real.rpow_def_of_pos hX,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      field_simp [hlog2]
    _ = _ := by rfl

end BoundedWordNormalizedRecurrence

end MarkedC4
end SymmetricSubgroupAsymptotics

end
