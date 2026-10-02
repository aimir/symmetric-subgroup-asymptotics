import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalRows

/-!
# Polynomial rows in the bounded numerical owner menu

The ordinary numerical catalogue contains finitely many bounded-width rows
whose coefficients are proved only up to a fixed polynomial.  This file takes
the maxima of those finitely many constants and degrees and absorbs the
resulting polynomial into the log-squared menu envelope.  No numerical
constant is assumed or normalized to one.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Numerical owner entries in the width range in which polynomial rows are
permitted. -/
abbrev PreE7BoundedNumericalOwnedIndex :=
  Σ fw : Fin 1025, PreE7NumericalOwnedIndex fw.1

private def HasPolynomialRow
    (z : PreE7BoundedNumericalOwnedIndex) : Prop :=
  ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ b,
    (preE7NumericalOwnedPackage z.2).package.certificate.D b ≤
      K * (1 + (b : ℝ)) ^ p

private noncomputable def boundedPolynomialConstant
    (z : PreE7BoundedNumericalOwnedIndex) : ℝ :=
  if h : HasPolynomialRow z then Classical.choose h else 1

private noncomputable def boundedPolynomialDegree
    (z : PreE7BoundedNumericalOwnedIndex) : ℕ :=
  if h : HasPolynomialRow z then
    Classical.choose (Classical.choose_spec h)
  else 0

private theorem boundedPolynomialConstant_nonneg
    (z : PreE7BoundedNumericalOwnedIndex)
    (h : HasPolynomialRow z) :
    0 ≤ boundedPolynomialConstant z := by
  rw [boundedPolynomialConstant, dif_pos h]
  exact (Classical.choose_spec
    (Classical.choose_spec h)).1

private theorem boundedPolynomialRow
    (z : PreE7BoundedNumericalOwnedIndex) (h : HasPolynomialRow z)
    (b : ℕ) :
    (preE7NumericalOwnedPackage z.2).package.certificate.D b ≤
      boundedPolynomialConstant z *
        (1 + (b : ℝ)) ^ boundedPolynomialDegree z := by
  rw [boundedPolynomialConstant, dif_pos h,
    boundedPolynomialDegree, dif_pos h]
  exact (Classical.choose_spec
    (Classical.choose_spec h)).2 b

/-- A polynomial in the source size is bounded by a width-weighted
log-squared exponential on every menu summand. -/
theorem shiftedNatPow_le_widthLogSquared
    (p n w : ℕ) (hw : w ∈ Finset.Ico 3 (n + 1)) :
    (1 + ((n - w : ℕ) : ℝ)) ^ p ≤
      (2 : ℝ) ^
        ((p : ℝ) * w * Real.log ((n : ℝ) + 2) ^ 2) := by
  let X : ℝ := (n : ℝ) + 2
  have hww := Finset.mem_Ico.mp hw
  have hX4 : (4 : ℝ) ≤ X := by
    have : 3 ≤ n := hww.1.trans (by omega)
    dsimp [X]
    exact_mod_cast (show 4 ≤ n + 2 by omega)
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX4
  have hlogtwo : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogone : 1 ≤ Real.log X := by
    have hm : Real.log (4 : ℝ) ≤ Real.log X :=
      Real.log_le_log (by norm_num) hX4
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hm
    norm_num at hm
    linarith
  have hlogb : Real.logb 2 X ≤ 2 * Real.log X := by
    rw [Real.logb]
    have hden : 0 < Real.log 2 := hlogtwo.trans' (by norm_num)
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (zero_le_one.trans hlogone)
      (sub_nonneg.mpr hlogtwo.le)]
  have hwidth : 2 * Real.log X ≤ (w : ℝ) * Real.log X ^ 2 := by
    have hwR : (3 : ℝ) ≤ w := by exact_mod_cast hww.1
    nlinarith [sq_nonneg (Real.log X - 1)]
  have hexp : (p : ℝ) * Real.logb 2 X ≤
      (p : ℝ) * w * Real.log X ^ 2 := by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left (hlogb.trans hwidth) (Nat.cast_nonneg p))
  have hbase : (1 : ℝ) + (n - w : ℕ) ≤ X := by
    dsimp [X]
    exact_mod_cast (show 1 + (n - w) ≤ n + 2 by omega)
  calc
    (1 + ((n - w : ℕ) : ℝ)) ^ p ≤ X ^ p := by gcongr
    _ = X ^ (p : ℝ) := by rw [Real.rpow_natCast]
    _ = ((2 : ℝ) ^ Real.logb 2 X) ^ (p : ℝ) := by
      rw [Real.rpow_logb (by norm_num) (by norm_num) hXpos]
    _ = (2 : ℝ) ^ (Real.logb 2 X * p) := by
      rw [← Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ ((p : ℝ) * Real.logb 2 X) := by
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- Uniform constants obtained from the finite bounded-width menu. -/
private noncomputable def boundedPolynomialConstantUpper : ℝ :=
  Classical.choose (Finite.exists_le boundedPolynomialConstant)

private theorem boundedPolynomialConstant_le_upper
    (z : PreE7BoundedNumericalOwnedIndex) :
    boundedPolynomialConstant z ≤ boundedPolynomialConstantUpper :=
  Classical.choose_spec (Finite.exists_le boundedPolynomialConstant) z

private noncomputable def boundedPolynomialDegreeUpper : ℕ :=
  Classical.choose (Finite.exists_le boundedPolynomialDegree)

private theorem boundedPolynomialDegree_le_upper
    (z : PreE7BoundedNumericalOwnedIndex) :
    boundedPolynomialDegree z ≤ boundedPolynomialDegreeUpper :=
  Classical.choose_spec (Finite.exists_le boundedPolynomialDegree) z

noncomputable def preE7NumericalOwnedPolynomialConstant : ℝ :=
  max 1 boundedPolynomialConstantUpper

noncomputable def preE7NumericalOwnedPolynomialDegree : ℕ :=
  boundedPolynomialDegreeUpper

theorem preE7NumericalOwnedPolynomialConstant_pos :
    0 < preE7NumericalOwnedPolynomialConstant := by
  unfold preE7NumericalOwnedPolynomialConstant
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- Every ordinary numerical row, including the polynomial bounded-width
rows, satisfies one common log-squared envelope. -/
theorem preE7NumericalOwned_main_le
    (n w : ℕ) (hw : w ∈ Finset.Ico 3 (n + 1))
    (a : PreE7NumericalOwnedIndex w) :
    (preE7NumericalOwnedPackage a).package.certificate.D (n - w) ≤
      preE7NumericalOwnedPolynomialConstant *
        (2 : ℝ) ^
          ((16 + (preE7NumericalOwnedPolynomialDegree : ℝ)) * w *
            Real.log ((n : ℝ) + 2) ^ 2) := by
  rcases (preE7NumericalOwnedPackage a).main_total_growth with hmain | hpoly
  · have hwb : w + (n - w) + 2 = n + 2 := by
      have := (Finset.mem_Ico.mp hw).2
      omega
    have hold := hmain (n - w)
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
    have hw0 : (0 : ℝ) ≤ w := by positivity
    calc
      _ ≤ (2 : ℝ) ^
          (16 * (w : ℝ) *
            Real.log ((w + (n - w) + 2 : ℕ) : ℝ) ^ 2) := hold
      _ ≤ preE7NumericalOwnedPolynomialConstant *
          (2 : ℝ) ^
            ((16 + (preE7NumericalOwnedPolynomialDegree : ℝ)) * w *
              Real.log ((n : ℝ) + 2) ^ 2) := by
        rw [hwb]
        have hpow : (2 : ℝ) ^
              (16 * (w : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) ^ 2) ≤
            (2 : ℝ) ^
              ((16 + (preE7NumericalOwnedPolynomialDegree : ℝ)) * w *
                Real.log ((n : ℝ) + 2) ^ 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hp0 : (0 : ℝ) ≤ preE7NumericalOwnedPolynomialDegree := by
            positivity
          norm_num
          nlinarith [mul_nonneg hp0 (mul_nonneg hw0 hlog)]
        exact hpow.trans (by
          nth_rewrite 1 [← one_mul ((2 : ℝ) ^ _)]
          exact mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ preE7NumericalOwnedPolynomialConstant by
              unfold preE7NumericalOwnedPolynomialConstant
              exact le_max_left _ _)
            (by positivity))
  · rcases hpoly with ⟨hw1024, K, p, hK, hrow⟩
    let fw : Fin 1025 := ⟨w, by omega⟩
    let z : PreE7BoundedNumericalOwnedIndex := ⟨fw, a⟩
    have hzpoly : HasPolynomialRow z := by
      exact ⟨K, p, hK, hrow⟩
    have hconst : boundedPolynomialConstant z ≤
        preE7NumericalOwnedPolynomialConstant := by
      exact boundedPolynomialConstant_le_upper z |>.trans (le_max_right _ _)
    have hdegree : boundedPolynomialDegree z ≤
        preE7NumericalOwnedPolynomialDegree := by
      exact boundedPolynomialDegree_le_upper z
    have hrowz := boundedPolynomialRow z hzpoly (n - w)
    have hbase : (1 : ℝ) ≤ 1 + (n - w : ℕ) := by
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hpow : (1 + ((n - w : ℕ) : ℝ)) ^ boundedPolynomialDegree z ≤
        (1 + ((n - w : ℕ) : ℝ)) ^ preE7NumericalOwnedPolynomialDegree :=
      pow_le_pow_right₀ hbase hdegree
    have hshift := shiftedNatPow_le_widthLogSquared
      preE7NumericalOwnedPolynomialDegree n w hw
    calc
      _ ≤ boundedPolynomialConstant z *
          (1 + ((n - w : ℕ) : ℝ)) ^ boundedPolynomialDegree z := by
        simpa [z] using hrowz
      _ ≤ preE7NumericalOwnedPolynomialConstant *
          (1 + ((n - w : ℕ) : ℝ)) ^ boundedPolynomialDegree z :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ ≤ preE7NumericalOwnedPolynomialConstant *
          (1 + ((n - w : ℕ) : ℝ)) ^ preE7NumericalOwnedPolynomialDegree :=
        mul_le_mul_of_nonneg_left hpow
          preE7NumericalOwnedPolynomialConstant_pos.le
      _ ≤ preE7NumericalOwnedPolynomialConstant *
          (2 : ℝ) ^
            ((preE7NumericalOwnedPolynomialDegree : ℝ) * w *
              Real.log ((n : ℝ) + 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hshift
          preE7NumericalOwnedPolynomialConstant_pos.le
      _ ≤ preE7NumericalOwnedPolynomialConstant *
          (2 : ℝ) ^
            ((16 + (preE7NumericalOwnedPolynomialDegree : ℝ)) * w *
              Real.log ((n : ℝ) + 2) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _
          preE7NumericalOwnedPolynomialConstant_pos.le
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hlog : 0 ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
        have hw0 : (0 : ℝ) ≤ w := by positivity
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 by norm_num)
          (mul_nonneg hw0 hlog)]

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
