import SymmetricSubgroupAsymptotics.GaussianEstimates
import SymmetricSubgroupAsymptotics.ElementaryParity

/-!
# Uniform summation of the exceptional-lift incidence kernel

The retained relation dimension is summed jointly with the image dimension.
Completing the square leaves a translate of one summable Gaussian on the
half-integer lattice and a geometric bound in the relation dimension.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- A common majorant for both parity classes of all shifted Gaussian sums. -/
def halfLatticeGaussian (j : ℤ) : ℝ := (2 : ℝ) ^ (-(j : ℝ) ^ 2 / 4)

theorem halfLatticeGaussian_pos (j : ℤ) : 0 < halfLatticeGaussian j :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem halfLatticeGaussian_nat_summable :
    Summable (fun n : ℕ ↦ halfLatticeGaussian n) := by
  refine (summable_geometric_two.mul_left 2).of_nonneg_of_le
    (fun n ↦ (halfLatticeGaussian_pos n).le) fun n ↦ ?_
  have hp : (2 : ℝ) ^ (1 - (n : ℝ)) = 2 * (1 / 2 : ℝ) ^ n := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_one, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    simp [one_div, inv_pow]
  rw [← hp]
  unfold halfLatticeGaussian
  push_cast
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [sq_nonneg ((n : ℝ) - 2)]

theorem halfLatticeGaussian_summable : Summable halfLatticeGaussian := by
  apply halfLatticeGaussian_nat_summable.of_nat_of_neg
  simpa only [halfLatticeGaussian, Int.cast_neg, even_two, Even.neg_pow] using
    halfLatticeGaussian_nat_summable

/-- A finite positive constant, independent of every orbit profile. -/
def halfLatticeGaussianSum : ℝ := ∑' j : ℤ, halfLatticeGaussian j

theorem halfLatticeGaussianSum_pos : 0 < halfLatticeGaussianSum :=
  halfLatticeGaussian_summable.tsum_pos (fun j ↦ (halfLatticeGaussian_pos j).le)
    0 (halfLatticeGaussian_pos 0)

/-- The same constant controls every shift and every finite summation range. -/
theorem shiftedGaussian_sum_le (R l : ℕ) (s : Finset ℕ) :
    ∑ k ∈ s, (2 : ℝ) ^ (-((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2) ≤
      halfLatticeGaussianSum := by
  let a : ℕ → ℤ := fun k ↦ 2 * (k : ℤ) + l - R
  have ha : Function.Injective a := by
    intro i j h
    dsimp [a] at h
    omega
  have ht (k : ℕ) :
      (2 : ℝ) ^ (-((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2) =
        halfLatticeGaussian (a k) := by
    unfold halfLatticeGaussian a
    push_cast
    congr 1
    ring
  simp_rw [ht]
  rw [← Finset.sum_image (fun i _ j _ h ↦ ha h)]
  exact halfLatticeGaussian_summable.sum_le_tsum _
    (fun j _ ↦ (halfLatticeGaussian_pos j).le)

/-- The local realization constant is absorbed uniformly in the retained
relation dimension. This deliberately uses a generous absolute constant. -/
theorem exceptionalRelation_kernel_le (d : ℝ) (hd : 0 ≤ d)
    (l : ℕ) (hl : 1 ≤ l) :
    (72 : ℝ) ^ l * (2 : ℝ) ^ (-(l : ℝ) * d - 3 * (l : ℝ) ^ 2 / 4) ≤
      (2 : ℝ) ^ (64 : ℕ) * (2 : ℝ) ^ (-d) * (1 / 2 : ℝ) ^ l := by
  have hp : (72 : ℝ) ^ l ≤ (2 : ℝ) ^ (7 * (l : ℝ)) := by
    calc
      _ ≤ ((2 : ℝ) ^ (7 : ℕ)) ^ l := pow_le_pow_left₀ (by norm_num) (by norm_num) l
      _ = _ := by rw [← pow_mul, ← Real.rpow_natCast]; push_cast; rfl
  have he : 7 * (l : ℝ) + (-(l : ℝ) * d - 3 * (l : ℝ) ^ 2 / 4) ≤
      64 - d - (l : ℝ) := by
    have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hld : d ≤ (l : ℝ) * d := by nlinarith
    nlinarith [sq_nonneg ((l : ℝ) - 6)]
  calc
    _ ≤ (2 : ℝ) ^ (7 * (l : ℝ)) *
        (2 : ℝ) ^ (-(l : ℝ) * d - 3 * (l : ℝ) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (2 : ℝ) ^ (7 * (l : ℝ) +
        (-(l : ℝ) * d - 3 * (l : ℝ) ^ 2 / 4)) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (64 - d - (l : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      norm_num [one_div, inv_pow]
      left
      rw [← inv_pow]
      norm_num

/-- Square completion, including the parity term of the central Gaussian
coefficient. No integer floor is suppressed in this identity. -/
theorem exceptionalIncidence_exponent (R t k l : ℕ) :
    (k : ℝ) * ((R : ℝ) - k) - (gaussianPower R : ℝ) -
        (l : ℝ) * ((k : ℝ) - t + l) =
      (R % 2 : ℕ) / 4 - ((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2 -
        (l : ℝ) * ((R : ℝ) / 2 - t) - 3 * (l : ℝ) ^ 2 / 4 := by
  rw [gaussianPower_quadratic]
  ring

/-- A uniform double-sum bound for the exact quadratic incidence exponent.
The range may contain all possible image dimensions and relation dimensions. -/
theorem exceptionalIncidence_kernel_sum_le (R t : ℕ)
    (hd : 0 ≤ (R : ℝ) / 2 - t) :
    ∑ l ∈ Finset.Icc 1 t, ∑ k ∈ Finset.range (R + 1),
      (72 : ℝ) ^ l * (2 : ℝ) ^ ((k : ℝ) * ((R : ℝ) - k) -
        (gaussianPower R : ℝ) - (l : ℝ) * ((k : ℝ) - t + l)) ≤
      ((2 : ℝ) ^ (66 : ℕ) * halfLatticeGaussianSum) *
        (2 : ℝ) ^ (-((R : ℝ) / 2 - t)) := by
  let d : ℝ := (R : ℝ) / 2 - t
  have hp : (2 : ℝ) ^ ((R % 2 : ℕ) / 4 : ℝ) ≤ 2 := by
    have hr : ((R % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show R % 2 ≤ 1 by omega)
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  have hterm (l : ℕ) (hl : l ∈ Finset.Icc 1 t) (k : ℕ) :
      (72 : ℝ) ^ l * (2 : ℝ) ^ ((k : ℝ) * ((R : ℝ) - k) -
        (gaussianPower R : ℝ) - (l : ℝ) * ((k : ℝ) - t + l)) ≤
      ((2 : ℝ) ^ (65 : ℕ) * (2 : ℝ) ^ (-d) * (1 / 2 : ℝ) ^ l) *
        (2 : ℝ) ^ (-((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2) := by
    have hrel := exceptionalRelation_kernel_le d hd l (Finset.mem_Icc.mp hl).1
    rw [exceptionalIncidence_exponent]
    have he : (R % 2 : ℕ) / 4 -
        ((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2 -
        (l : ℝ) * ((R : ℝ) / 2 - t) - 3 * (l : ℝ) ^ 2 / 4 =
        ((R % 2 : ℕ) / 4 : ℝ) +
        (-(l : ℝ) * d - 3 * (l : ℝ) ^ 2 / 4) +
        (-((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2) := by dsimp [d]; ring
    rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      _ = (2 : ℝ) ^ ((R % 2 : ℕ) / 4 : ℝ) *
          ((72 : ℝ) ^ l * (2 : ℝ) ^ (-(l : ℝ) * d - 3 * (l : ℝ) ^ 2 / 4)) *
          (2 : ℝ) ^ (-((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2) := by ring
      _ ≤ 2 * ((2 : ℝ) ^ (64 : ℕ) * (2 : ℝ) ^ (-d) * (1 / 2 : ℝ) ^ l) *
          (2 : ℝ) ^ (-((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hp hrel (by positivity) (by norm_num))
          (by positivity)
      _ = _ := by rw [show (65 : ℕ) = 64 + 1 from rfl, pow_succ]; ring
  calc
    _ ≤ ∑ l ∈ Finset.Icc 1 t,
        ((2 : ℝ) ^ (65 : ℕ) * (2 : ℝ) ^ (-d) * (1 / 2 : ℝ) ^ l) *
          halfLatticeGaussianSum := by
      apply Finset.sum_le_sum
      intro l hl
      calc
        _ ≤ ∑ k ∈ Finset.range (R + 1),
            ((2 : ℝ) ^ (65 : ℕ) * (2 : ℝ) ^ (-d) * (1 / 2 : ℝ) ^ l) *
            (2 : ℝ) ^ (-((k : ℝ) + (l : ℝ) / 2 - (R : ℝ) / 2) ^ 2) :=
          Finset.sum_le_sum (fun k _ ↦ hterm l hl k)
        _ = _ := by rw [← Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (shiftedGaussian_sum_le R l _)
          (by positivity)
    _ = ((2 : ℝ) ^ (65 : ℕ) * halfLatticeGaussianSum * (2 : ℝ) ^ (-d)) *
        ∑ l ∈ Finset.Icc 1 t, (1 / 2 : ℝ) ^ l := by rw [Finset.mul_sum]; congr 1; ext l; ring
    _ ≤ ((2 : ℝ) ^ (65 : ℕ) * halfLatticeGaussianSum * (2 : ℝ) ^ (-d)) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [halfLatticeGaussianSum_pos])
      calc
        _ ≤ ∑' l : ℕ, (1 / 2 : ℝ) ^ l :=
          summable_geometric_two.sum_le_tsum _ (fun _ _ ↦ by positivity)
        _ = 2 := tsum_geometric_two
    _ = _ := by rw [show (66 : ℕ) = 65 + 1 from rfl, pow_succ]; dsimp [d]; ring

end SymmetricSubgroupAsymptotics
