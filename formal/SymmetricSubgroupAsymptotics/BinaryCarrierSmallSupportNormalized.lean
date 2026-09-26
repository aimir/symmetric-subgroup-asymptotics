import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalSmallSupport

/-! An explicit normalized fixed-model estimate. The source order bounds
only the number of original tails; the one-dimension gap in the terminal
Gaussian weight is the proved gap of those original tails. No asymptotic
cutoff, supplied subgroup count, or physical denominator is an input. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportNormalized

open BinaryCarrierOriginalSmallSupport BinaryCarrierOriginalCyclicFourHall

/-- The explicit finite subspace count has the usual elementary upper
bound, including its exact q+1 summation length. -/
theorem subspaceCount_le (q : ℕ) :
    (binarySubspaceCount q : ℝ) ≤
      ((q : ℝ)+1) * eulerProduct⁻¹ * (2 : ℝ)^((q : ℝ)^2/4) := by
  have he : (binarySubspaceCount q : ℝ) = terminalGaussianWeight q 0 := by
    have h : (binarySubspaceCount q : ℝ) = (binaryGaussianSum q : ℝ) := by
      exact_mod_cast binarySubspaceCount_eq_gaussianSum q
    rw [h]
    simp [terminalGaussianWeight, binaryGaussianSum]
  rw [he]
  simpa using terminalGaussianWeight_le_quadratic q 0

/-- The order exponent is at most 7C/4, not 7C. -/
theorem exponent_le (R C q : ℕ) (hq : 4*q ≤ 7*C) :
    (q : ℝ)^2/4 + ((C : ℝ)+7)^2/3 - ((R : ℝ)+C)/2 + 1/2 ≤
      -((R : ℝ)+C)/2 + 1/2 + (211/192)*(C : ℝ)^2 + (14/3)*C + 49/3 := by
  have hq' : 4*(q : ℝ) ≤ 7*(C : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hs : (4*(q : ℝ))^2 ≤ (7*(C : ℝ))^2 :=
    pow_le_pow_left₀ (by positivity) hq' 2
  nlinarith

theorem polynomial_le (R c C q : ℕ) (hc : c ≤ R) (hq : 4*q ≤ 7*C) :
    2 * ((q : ℝ)+1) * ((R : ℝ)+1)^2 * ((c : ℝ)+1) ≤
      4 * ((R : ℝ)+C+1)^4 := by
  have hc' : (c : ℝ) ≤ R := by exact_mod_cast hc
  have hq' : 4*(q : ℝ) ≤ 7*(C : ℝ) := by exact_mod_cast hq
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hq1 : (q : ℝ)+1 ≤ 2*((R : ℝ)+C+1) := by linarith
  have hR1 : (R : ℝ)+1 ≤ (R : ℝ)+C+1 := by linarith
  have hc1 : (c : ℝ)+1 ≤ (R : ℝ)+C+1 := by linarith
  have hp : ((R : ℝ)+1)^2 ≤ ((R : ℝ)+C+1)^2 :=
    pow_le_pow_left₀ (by positivity) hR1 2
  have hm := mul_le_mul
    (mul_le_mul hq1 hp (by positivity) (by positivity)) hc1
      (by positivity) (by positivity)
  calc
    _ = 2 * (((q : ℝ)+1)*((R : ℝ)+1)^2*((c : ℝ)+1)) := by ring
    _ ≤ 2 * ((2*((R : ℝ)+C+1))*((R : ℝ)+C+1)^2*((R : ℝ)+C+1)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

def bound (R C : ℕ) : ℝ :=
  4 * (eulerProduct⁻¹)^6 * ((R : ℝ)+C+1)^4 *
    (2 : ℝ)^(-((R : ℝ)+C)/2 + 1/2 +
      (211/192)*(C : ℝ)^2 + (14/3)*C + 49/3)

/-- Scalar normalization of the actual-tail estimate. All polynomial and
Euler factors remain explicit; positive C supplies the original rank gap. -/
theorem weight_bound_div_gaussian_le (R c C q : ℕ)
    (hC : 0 < C) (hc : c ≤ R) (hq : 4*q ≤ 7*C) :
    ((binarySubspaceCount q : ℝ) * BinaryTerminalFullTailCount.prefactor R c C *
      terminalGaussianWeight R (C-1)) / (binaryGaussianSum (R+C) : ℝ) ≤ bound R C := by
  let G := (binarySubspaceCount q : ℝ)
  let A := BinaryTerminalFullTailCount.prefactor R c C
  let X := terminalGaussianWeight R (C-1) / (binaryGaussianSum (R+C) : ℝ)
  have hG : G ≤ ((q : ℝ)+1) * eulerProduct⁻¹ * (2 : ℝ)^((q : ℝ)^2/4) :=
    subspaceCount_le q
  have hX : X ≤ (eulerProduct⁻¹)^2 * ((R : ℝ)+1) *
      (2 : ℝ)^(-((R : ℝ)+C)/2+1/2) :=
    terminalGaussianWeight_div_gaussian_le_rank_gap R (C-1) C (by omega)
  have hA : 0 ≤ A := BinaryTerminalFullTailCount.prefactor_nonneg R c C
  have hX0 : 0 ≤ X := by
    exact div_nonneg (terminalGaussianWeight_pos R (C-1)).le
      (by exact_mod_cast (binaryGaussianSum_pos (R+C)).le)
  have hGup0 : 0 ≤ ((q : ℝ)+1) * eulerProduct⁻¹ * (2 : ℝ)^((q : ℝ)^2/4) := by
    positivity [euler_positive]
  have hmain := mul_le_mul
    (mul_le_mul_of_nonneg_right hG hA) hX hX0 (mul_nonneg hGup0 hA)
  have hexp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (exponent_le R C q hq)
  have hpowers :
      (2 : ℝ)^((q : ℝ)^2/4 + ((C : ℝ)+7)^2/3 - ((R : ℝ)+C)/2+1/2) =
        (2 : ℝ)^((q : ℝ)^2/4) * (2 : ℝ)^(((C : ℝ)+7)^2/3) *
          (2 : ℝ)^(-((R : ℝ)+C)/2+1/2) := by
    rw [show (q : ℝ)^2/4 + ((C : ℝ)+7)^2/3 - ((R : ℝ)+C)/2+1/2 =
      (q : ℝ)^2/4 + ((C : ℝ)+7)^2/3 + (-((R : ℝ)+C)/2+1/2) by ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = G * A * X := by dsimp [G, A, X]; ring
    _ ≤ (((q : ℝ)+1) * eulerProduct⁻¹ * (2 : ℝ)^((q : ℝ)^2/4) * A) *
        ((eulerProduct⁻¹)^2 * ((R : ℝ)+1) *
          (2 : ℝ)^(-((R : ℝ)+C)/2+1/2)) := hmain
    _ = (2 * ((q : ℝ)+1) * ((R : ℝ)+1)^2 * ((c : ℝ)+1)) *
        (eulerProduct⁻¹)^6 *
          (2 : ℝ)^((q : ℝ)^2/4 + ((C : ℝ)+7)^2/3 - ((R : ℝ)+C)/2+1/2) := by
      dsimp [A, BinaryTerminalFullTailCount.prefactor]
      rw [hpowers]
      ring
    _ ≤ (4 * ((R : ℝ)+C+1)^4) * (eulerProduct⁻¹)^6 *
          (2 : ℝ)^(-((R : ℝ)+C)/2+1/2+(211/192)*(C : ℝ)^2+(14/3)*C+49/3) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (polynomial_le R c C q hc hq)
        (by positivity)) hexp (by positivity) (by positivity)
    _ = _ := by unfold bound; ring

variable (a : ℕ) (m : CarrierTarget → ℕ) {L : ℕ}
    (occurrences : Fin L ≃ (Σ t, Fin (m t)))

include occurrences in
/-- The normalized count of the original fixed model. No tail mark or
subgroup-count bound is supplied by the caller. -/
theorem modelFamily_card_div_gaussian_le (p : CriticalProfile)
    (hC : 0 < halfSupport a m)
    (P : Subgroup (Equiv.Perm (ModelPoints p a m)) → Prop) :
    (Nat.card (ModelFamily p a m P) : ℝ) /
      (binaryGaussianSum (p.rank + halfSupport a m) : ℝ) ≤ bound p.rank (halfSupport a m) := by
  have hc : p.d8+p.e8 ≤ p.rank := by
    have h := terminalCritical_two_card_le_rank p.abelianRank (criticalProfileNonabelianChoice p)
    simp only [criticalProfile_product_rank, CriticalProfileNonabelianIndex,
      Fintype.card_sum, Fintype.card_fin] at h
    omega
  calc
    _ ≤ BinaryCarrierOriginalSmallSupport.bound a m p /
        (binaryGaussianSum (p.rank + halfSupport a m) : ℝ) :=
      div_le_div_of_nonneg_right
        (modelFamily_card_le a m occurrences p hC P)
        (by exact_mod_cast (binaryGaussianSum_pos (p.rank + halfSupport a m)).le)
    _ ≤ _ := weight_bound_div_gaussian_le p.rank (p.d8+p.e8) (halfSupport a m)
      (sourceOrder a m) hC hc (sourceOrder_le_halfSupport a m occurrences)

end SymmetricSubgroupAsymptotics.BinaryCarrierSmallSupportNormalized
