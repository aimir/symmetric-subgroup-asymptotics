import SymmetricSubgroupAsymptotics.BinaryPairMomentNormalized
import SymmetricSubgroupAsymptotics.MarkerZeroDefect

/-!
# The odd zero-defect binary-error transfer

The empty odd state contributes the singleton coefficient `alpha_N`.  The
single natural marker contributes `beta_N` times the actual pair-orbit first
moment.  The complete binary pair-moment theorem eliminates that first
moment, leaving only the two unmarked binary error ratios in degrees `2N`
and `2(N-1)`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OddMarkerBinaryErrorTransfer

open MarkerZeroDefect BinaryPairMomentNormalized

def currentCoefficient (N : ℕ) : ℝ :=
  alpha N + beta N * (7 + (6*N : ℝ) ^ (1/4 : ℝ))

def predecessorErrorCoefficient (N : ℕ) : ℝ :=
  beta N * predecessorCoefficient N

theorem beta_nonneg (N : ℕ) : 0 ≤ beta N := by
  unfold beta alpha
  have hc : (0 : ℝ) ≤ criticalCoefficient N := by
    exact_mod_cast (criticalCoefficient_nonneg N)
  have hp : (0 : ℝ) < analyticParityCoefficient 1 N := by
    exact_mod_cast analyticParityCoefficient_positive 1 N
  positivity

/-- The exact numerical form used by the odd zero-defect row.  No
uncontrolled scalar or residual pair moment remains. -/
theorem binary_error_transfer (N : ℕ) (hN : 1 ≤ N) :
    alpha N * binaryErrorRatio N + beta N * pairErrorMomentRatio N ≤
      currentCoefficient N * binaryErrorRatio N +
        predecessorErrorCoefficient N * binaryErrorRatio (N-1) := by
  have hm := complete_binary_pair_moment N hN
  calc
    alpha N * binaryErrorRatio N + beta N * pairErrorMomentRatio N ≤
        alpha N * binaryErrorRatio N + beta N *
          ((7 + (6*N : ℝ) ^ (1/4 : ℝ)) * binaryErrorRatio N +
            predecessorCoefficient N * binaryErrorRatio (N-1)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (beta_nonneg N))
    _ = currentCoefficient N * binaryErrorRatio N +
        predecessorErrorCoefficient N * binaryErrorRatio (N-1) := by
      unfold currentCoefficient predecessorErrorCoefficient
      ring

end SymmetricSubgroupAsymptotics.OddMarkerBinaryErrorTransfer

end

