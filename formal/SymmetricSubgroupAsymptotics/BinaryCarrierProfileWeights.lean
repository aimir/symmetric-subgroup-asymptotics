import SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile
import SymmetricSubgroupAsymptotics.FiniteFactorialProfiles
import SymmetricSubgroupAsymptotics.WeightedCriticalAssembly

/-!
# Summing the original carrier profile weights

The critical profile weight is factored out of the literal mixed-action
denominator. Every carrier colour retains its own original normalizer and
occurrence factorial. A finite family of carrier profiles then costs a
constant depending only on the number of colours; exact normalizer orders
and an identification of different colours are unnecessary.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierProfileWeights

variable {ι : Type} [Fintype ι] (Ω : ι → Type)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))

/-- The normalizer of the original physical action, before any quotient
replacement or choice of a carrier master. -/
def normalizerOrder (i : ι) : ℝ :=
  Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i))))

theorem normalizerOrder_one_le (i : ι) : 1 ≤ normalizerOrder Ω U i := by
  unfold normalizerOrder
  exact_mod_cast (Nat.card_pos (α :=
    Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))))

theorem originalDenominator_reciprocal (p : CriticalProfile) (m : ι → ℕ) :
    1 / BinaryCarrierMixedProfile.originalDenominator Ω U p m =
      (p.weight : ℝ) * FiniteFactorialProfiles.weight (normalizerOrder Ω U) m := by
  have hc :
      (∏ i, (Nat.card (Subgroup.normalizer (criticalActionSubgroup i :
        Set (Equiv.Perm (criticalActionPoints i)))) : ℝ) ^ p.multiplicity i *
          ((p.multiplicity i).factorial : ℝ))⁻¹ = (p.weight : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) p.original_normalizer_weight
    simpa only [Rat.cast_inv, Rat.cast_prod, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast] using h
  rw [one_div, BinaryCarrierMixedProfile.originalDenominator,
    Fintype.prod_sum_type, mul_inv_rev]
  change (∏ i, normalizerOrder Ω U i ^ m i * ((m i).factorial : ℝ))⁻¹ *
    (∏ i, (Nat.card (Subgroup.normalizer (criticalActionSubgroup i :
      Set (Equiv.Perm (criticalActionPoints i)))) : ℝ) ^ p.multiplicity i *
        ((p.multiplicity i).factorial : ℝ))⁻¹ = _
  rw [hc, FiniteFactorialProfiles.weight_eq_reciprocal_denominator, one_div]
  exact mul_comm _ _

/-- The carrier profile set can depend on the original critical profile.
No unrestricted infinite sum or coverage hypothesis is used. -/
theorem sum_reciprocal_le (p : CriticalProfile) (S : Finset (ι → ℕ)) :
    ∑ m ∈ S, 1 / BinaryCarrierMixedProfile.originalDenominator Ω U p m ≤
      (p.weight : ℝ) * Real.exp (Fintype.card ι : ℝ) := by
  simp only [originalDenominator_reciprocal, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (FiniteFactorialProfiles.sum_le_exp_card S (normalizerOrder Ω U)
      (normalizerOrder_one_le Ω U)) (by exact_mod_cast p.weight_pos.le)

/-- Sum all critical profiles of one rank, retaining the exact critical
coefficient instead of bounding it by an exponential in the colour count. -/
theorem critical_profile_sum_reciprocal_le (R : ℕ)
    (S : CriticalProfile → Finset (ι → ℕ)) :
    ∑ p : criticalProfiles R, ∑ m ∈ S p.1,
      1 / BinaryCarrierMixedProfile.originalDenominator Ω U p.1 m ≤
        (criticalCoefficient R : ℝ) * Real.exp (Fintype.card ι : ℝ) := by
  calc
    _ ≤ ∑ p : criticalProfiles R,
        (p.1.weight : ℝ) * Real.exp (Fintype.card ι : ℝ) :=
      Finset.sum_le_sum fun p _ => sum_reciprocal_le Ω U p.1 (S p.1)
    _ = _ := by rw [← Finset.sum_mul, criticalProfile_weight_sum_real]

/-- Insert a proved common model bound under the unchanged physical
weights. The bound is paid after the complete finite carrier-profile sum. -/
theorem sum_div_le (p : CriticalProfile) (S : Finset (ι → ℕ))
    (a : (ι → ℕ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ m ∈ S, a m ≤ C) :
    ∑ m ∈ S, a m / BinaryCarrierMixedProfile.originalDenominator Ω U p m ≤
      (p.weight : ℝ) * Real.exp (Fintype.card ι : ℝ) * C := by
  have hterm (m : ι → ℕ) :
      a m / BinaryCarrierMixedProfile.originalDenominator Ω U p m =
        (p.weight : ℝ) *
          (FiniteFactorialProfiles.weight (normalizerOrder Ω U) m * a m) := by
    rw [div_eq_mul_one_div, originalDenominator_reciprocal]
    ring
  simp only [hterm, ← Finset.mul_sum]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (FiniteFactorialProfiles.sum_mul_le_exp_card S (normalizerOrder Ω U)
      (normalizerOrder_one_le Ω U) a C hC ha) (by exact_mod_cast p.weight_pos.le)

end SymmetricSubgroupAsymptotics.BinaryCarrierProfileWeights
