import SymmetricSubgroupAsymptotics.TerminalRankRecords
import SymmetricSubgroupAsymptotics.TerminalGaussian
import SymmetricSubgroupAsymptotics.BinaryFrameEstimates

/-! Dividing by the original terminal record multiplicity. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The original ordered bases and lifts have one uniform positive lower
bound; this includes vertical rank zero. -/
theorem terminalRecordDivisor_lower (u d : ℕ) :
    eulerProduct * (2 : ℝ)^(u*(u+d)) ≤ (terminalRecordDivisor u d : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (binary_injection_product_lower u u le_rfl)
    (show 0 ≤ (2 : ℝ)^(u*d) by positivity)
  simpa only [terminalRecordDivisor,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    mul_assoc,← pow_add,← Nat.mul_add] using h

theorem terminalRecordDivisor_pos (u d : ℕ) : 0 < terminalRecordDivisor u d := by
  have h : (0 : ℝ) < (terminalRecordDivisor u d : ℝ) :=
    lt_of_lt_of_le (by positivity [euler_positive]) (terminalRecordDivisor_lower u d)
  exact_mod_cast h

/-- The literal rank-binned incidence count and central-fibre weight,
divided by every original ordered basis and linear lift. -/
def terminalRecordIncidenceTerm (r c d τ u l : ℕ) : ℝ :=
  (binaryGaussianCoefficient c l : ℝ) * (72 * (2 : ℝ)^τ)^l *
    (2 : ℝ)^((u+d)*(r-2*l)) * (2 : ℝ)^((u+d)*l) /
      (terminalRecordDivisor u d : ℝ)

theorem terminalRecordIncidenceTerm_le (r c d τ u l : ℕ)
    (hl : l ≤ c) (hr : 2*l ≤ r) :
    terminalRecordIncidenceTerm r c d τ u l ≤
      eulerProduct⁻¹ * (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l *
        (2 : ℝ)^((τ : ℝ)*l + ((r : ℝ)-u-l)*((u : ℝ)+d)) := by
  have hg : 0 ≤ (binaryGaussianCoefficient c l : ℝ) := by
    exact_mod_cast (binaryGaussianCoefficient_pos hl).le
  have hpow : ((2 : ℝ)^τ)^l * (2 : ℝ)^((u+d)*(r-2*l)) *
        (2 : ℝ)^((u+d)*l) / (2 : ℝ)^(u*(u+d)) =
      (2 : ℝ)^((τ : ℝ)*l + ((r : ℝ)-u-l)*((u : ℝ)+d)) := by
    rw [← pow_mul,← pow_add,← pow_add]
    simp only [← Real.rpow_natCast]
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast [Nat.cast_sub hr]
    ring
  unfold terminalRecordIncidenceTerm
  calc
    _ ≤ (binaryGaussianCoefficient c l : ℝ) * (72 * (2 : ℝ)^τ)^l *
        (2 : ℝ)^((u+d)*(r-2*l)) * (2 : ℝ)^((u+d)*l) /
        (eulerProduct * (2 : ℝ)^(u*(u+d))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity [euler_positive])
        (terminalRecordDivisor_lower u d)
    _ = (eulerProduct⁻¹ * (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l) *
        (((2 : ℝ)^τ)^l * (2 : ℝ)^((u+d)*(r-2*l)) *
          (2 : ℝ)^((u+d)*l) / (2 : ℝ)^(u*(u+d))) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hpow]

/-- Reindexing the original vertical rank gives the complete terminal
Gaussian numerator, including the zero relation stratum. -/
theorem terminalRecordIncidenceSum_le (r c d τ : ℕ) (hc : 2*c ≤ r) :
    (∑ u ∈ Finset.range (r+1), ∑ l ∈ Finset.range (c+1),
      terminalRecordIncidenceTerm r c d τ u l) ≤ terminalGaussianDoubleSum r c d τ := by
  let w : ℕ → ℝ := fun j => ∑ l ∈ Finset.range (c+1),
    (binaryGaussianCoefficient c l : ℝ) * (72 : ℝ)^l *
      (2 : ℝ)^((τ : ℝ)*l + ((j : ℝ)-l)*((r : ℝ)-j+d))
  have hw (j : ℕ) : 0 ≤ w j := by
    apply Finset.sum_nonneg
    intro l hl
    have hg : 0 ≤ (binaryGaussianCoefficient c l : ℝ) := by
      exact_mod_cast (binaryGaussianCoefficient_pos (by simpa using hl)).le
    positivity
  have hreindex : (∑ u ∈ Finset.range (r+1), w (r-u)) =
      ∑ j ∈ Finset.range (r+1), w j := by
    simpa using Finset.sum_range_reflect w (r+1)
  have hφ : 1 ≤ eulerProduct⁻¹ := by
    apply (one_le_inv₀ euler_positive).mpr
    simpa using eulerProduct_le_partial 0
  calc
    _ ≤ ∑ u ∈ Finset.range (r+1), eulerProduct⁻¹ * w (r-u) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l hl
      have hu' : u ≤ r := by simpa using hu
      have hl' : l ≤ c := by simpa using hl
      have h := terminalRecordIncidenceTerm_le r c d τ u l hl' (by omega)
      simpa only [Nat.cast_sub hu',sub_sub_cancel,mul_assoc] using h
    _ = eulerProduct⁻¹ * ∑ j ∈ Finset.range (r+1), w j := by
      rw [← Finset.mul_sum,hreindex]
    _ ≤ (eulerProduct⁻¹)^2 * ∑ j ∈ Finset.range (r+1), w j := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun j _ => hw j))
      nlinarith [sq_nonneg (eulerProduct⁻¹-1)]
    _ = _ := rfl

end SymmetricSubgroupAsymptotics
