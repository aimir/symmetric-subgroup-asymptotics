import SymmetricSubgroupAsymptotics.BinaryDuplicatePairIntrinsicIncidence
import SymmetricSubgroupAsymptotics.PermutationPairOrbitBudget
import SymmetricSubgroupAsymptotics.BinaryFamilies

/-!
# The complete binary pair moment in benchmark normalization

This is the normalization used by the ordinary recurrence and by the odd
zero-defect marker row.  The combinatorial Hall incidence is divided by the
exact even benchmark, and the lower pair moment is discharged by the sharp
original-point budget `t(H) <= N - 1`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryPairMomentNormalized

open PermutationPairOrbitMarks

/-- The non-factorial part of the exact even benchmark. -/
def pairScale (N : ℕ) : ℝ :=
  (binaryGaussianSum N : ℝ) * (criticalCoefficient N : ℝ)

theorem pairScale_pos (N : ℕ) : 0 < pairScale N := by
  unfold pairScale
  have hG : (0 : ℝ) < binaryGaussianSum N := by
    exact_mod_cast binaryGaussianSum_pos N
  have hc : (0 : ℝ) < criticalCoefficient N := by
    exact_mod_cast criticalCoefficient_pos N
  exact mul_pos hG hc

theorem exactBenchmark_even_scale (N : ℕ) :
    exactBenchmark (2*N) = ((2*N).factorial : ℝ) * pairScale N := by
  rw [exactBenchmark_even]
  simp only [pairScale]
  ring

/-- The normalized first moment of actual pair orbits in the complete
intrinsic noncritical fixed-point-free binary family. -/
def pairErrorMomentRatio (N : ℕ) : ℝ :=
  (∑ H : NoncriticalBinarySubgroups N,
      (Nat.card (PairOrbit H.val) : ℝ)) / exactBenchmark (2*N)

/-- The exact coefficient called `r_N` in the manuscript. -/
def predecessorCoefficient (N : ℕ) : ℝ :=
  ((N-1 : ℕ) : ℝ) / 4 * (pairScale (N-1) / pairScale N)

theorem pairErrorMomentRatio_eq_factorial (N : ℕ) :
    pairErrorMomentRatio N =
      ((∑ H : NoncriticalBinarySubgroups N,
          (Nat.card (PairOrbit H.val) : ℝ)) / (2*N).factorial) / pairScale N := by
  unfold pairErrorMomentRatio
  rw [exactBenchmark_even_scale]
  ring

theorem binaryErrorRatio_eq_factorial (N : ℕ) :
    binaryErrorRatio N =
      ((Nat.card (NoncriticalBinarySubgroups N) : ℝ) / (2*N).factorial) /
        pairScale N := by
  unfold binaryErrorRatio
  rw [exactBenchmark_even_scale]
  ring

/-- Every actual pair orbit consumes two distinct original points. -/
theorem pair_sum_le (N : ℕ) :
    (∑ H : NoncriticalBinarySubgroups N, Nat.card (PairOrbit H.val)) ≤
      N * Nat.card (NoncriticalBinarySubgroups N) := by
  calc
    (∑ H : NoncriticalBinarySubgroups N, Nat.card (PairOrbit H.val)) ≤
        ∑ _H : NoncriticalBinarySubgroups N, N := by
      apply Finset.sum_le_sum
      intro H _
      exact PermutationPairOrbitBudget.pairOrbit_card_fin_le N H.val
    _ = N * Nat.card (NoncriticalBinarySubgroups N) := by
      simp [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- The full manuscript pair-moment recurrence.  In particular, the
lower-degree first moment no longer appears on the right-hand side. -/
theorem complete_binary_pair_moment (N : ℕ) (hN : 1 ≤ N) :
    pairErrorMomentRatio N ≤
      (7 + (6*N : ℝ) ^ (1/4 : ℝ)) * binaryErrorRatio N +
        predecessorCoefficient N * binaryErrorRatio (N-1) := by
  have hrec :=
    BinaryDuplicatePairIntrinsicIncidence.intrinsic_normalized_pair_recurrence N hN
  have hscale : 0 < pairScale N := pairScale_pos N
  have hrecScaled := div_le_div_of_nonneg_right hrec hscale.le
  have hpairNat := pair_sum_le (N-1)
  have hpair :
      (∑ H : NoncriticalBinarySubgroups (N-1),
          (Nat.card (PairOrbit H.val) : ℝ)) ≤
        ((N-1 : ℕ) : ℝ) * Nat.card (NoncriticalBinarySubgroups (N-1)) := by
    exact_mod_cast hpairNat
  have hpairFactorial :
      (∑ H : NoncriticalBinarySubgroups (N-1),
          (Nat.card (PairOrbit H.val) : ℝ)) / (2*(N-1)).factorial ≤
        ((N-1 : ℕ) : ℝ) *
          ((Nat.card (NoncriticalBinarySubgroups (N-1)) : ℝ) /
            (2*(N-1)).factorial) := by
    calc
      _ ≤ (((N-1 : ℕ) : ℝ) * Nat.card (NoncriticalBinarySubgroups (N-1))) /
          (2*(N-1)).factorial :=
        div_le_div_of_nonneg_right hpair (by positivity)
      _ = _ := by ring
  calc
    pairErrorMomentRatio N =
        ((∑ H : NoncriticalBinarySubgroups N,
          (Nat.card (PairOrbit H.val) : ℝ)) / (2*N).factorial) / pairScale N :=
      pairErrorMomentRatio_eq_factorial N
    _ ≤ ((7 + (6*N : ℝ) ^ (1/4 : ℝ)) *
          ((Nat.card (NoncriticalBinarySubgroups N) : ℝ) / (2*N).factorial) +
        (1/4 : ℝ) *
          ((∑ H : NoncriticalBinarySubgroups (N-1),
            (Nat.card (PairOrbit H.val) : ℝ)) / (2*(N-1)).factorial)) /
          pairScale N := hrecScaled
    _ ≤ ((7 + (6*N : ℝ) ^ (1/4 : ℝ)) *
          ((Nat.card (NoncriticalBinarySubgroups N) : ℝ) / (2*N).factorial) +
        (1/4 : ℝ) * (((N-1 : ℕ) : ℝ) *
          ((Nat.card (NoncriticalBinarySubgroups (N-1)) : ℝ) /
            (2*(N-1)).factorial))) / pairScale N := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpairFactorial (by norm_num))
    _ = (7 + (6*N : ℝ) ^ (1/4 : ℝ)) * binaryErrorRatio N +
        predecessorCoefficient N * binaryErrorRatio (N-1) := by
      rw [binaryErrorRatio_eq_factorial N,
        binaryErrorRatio_eq_factorial (N-1)]
      unfold predecessorCoefficient
      have hp : pairScale (N-1) ≠ 0 := (pairScale_pos (N-1)).ne'
      have hn : pairScale N ≠ 0 := hscale.ne'
      field_simp

end SymmetricSubgroupAsymptotics.BinaryPairMomentNormalized

end
