import SymmetricSubgroupAsymptotics.Non2PreE7NumericalOwnedPolynomialEnvelope

/-!
# Polynomial tail rows in the bounded numerical owner menu

Some finite imprimitive-affine rows have a literal tail coefficient which is
polynomial in the source degree, but whose finite constant is too large for a
pointwise coefficient-one menu estimate.  Width is bounded by `12288` on
these rows.  This file takes the two maxima over that finite index and absorbs
the resulting polynomial into the global subquadratic menu envelope.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

abbrev PreE7BoundedTailNumericalOwnedIndex :=
  Σ fw : Fin 12289, PreE7NumericalOwnedIndex fw.1

private def HasPolynomialTail
    (z : PreE7BoundedTailNumericalOwnedIndex) : Prop :=
  ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ b,
    (preE7NumericalOwnedPackage z.2).package.certificate.T b ≤
      K * (1 + (b : ℝ)) ^ p

private noncomputable def boundedTailPolynomialConstant
    (z : PreE7BoundedTailNumericalOwnedIndex) : ℝ :=
  if h : HasPolynomialTail z then Classical.choose h else 1

private noncomputable def boundedTailPolynomialDegree
    (z : PreE7BoundedTailNumericalOwnedIndex) : ℕ :=
  if h : HasPolynomialTail z then
    Classical.choose (Classical.choose_spec h)
  else 0

private theorem boundedTailPolynomialConstant_nonneg
    (z : PreE7BoundedTailNumericalOwnedIndex)
    (h : HasPolynomialTail z) :
    0 ≤ boundedTailPolynomialConstant z := by
  rw [boundedTailPolynomialConstant, dif_pos h]
  exact (Classical.choose_spec (Classical.choose_spec h)).1

private theorem boundedTailPolynomialRow
    (z : PreE7BoundedTailNumericalOwnedIndex) (h : HasPolynomialTail z)
    (b : ℕ) :
    (preE7NumericalOwnedPackage z.2).package.certificate.T b ≤
      boundedTailPolynomialConstant z *
        (1 + (b : ℝ)) ^ boundedTailPolynomialDegree z := by
  rw [boundedTailPolynomialConstant, dif_pos h,
    boundedTailPolynomialDegree, dif_pos h]
  exact (Classical.choose_spec (Classical.choose_spec h)).2 b

private noncomputable def boundedTailPolynomialConstantUpper : ℝ :=
  Classical.choose (Finite.exists_le boundedTailPolynomialConstant)

private theorem boundedTailPolynomialConstant_le_upper
    (z : PreE7BoundedTailNumericalOwnedIndex) :
    boundedTailPolynomialConstant z ≤ boundedTailPolynomialConstantUpper :=
  Classical.choose_spec (Finite.exists_le boundedTailPolynomialConstant) z

private noncomputable def boundedTailPolynomialDegreeUpper : ℕ :=
  Classical.choose (Finite.exists_le boundedTailPolynomialDegree)

private theorem boundedTailPolynomialDegree_le_upper
    (z : PreE7BoundedTailNumericalOwnedIndex) :
    boundedTailPolynomialDegree z ≤ boundedTailPolynomialDegreeUpper :=
  Classical.choose_spec (Finite.exists_le boundedTailPolynomialDegree) z

noncomputable def preE7NumericalOwnedTailPolynomialConstant : ℝ :=
  max 1 boundedTailPolynomialConstantUpper

noncomputable def preE7NumericalOwnedTailPolynomialDegree : ℕ :=
  boundedTailPolynomialDegreeUpper

theorem preE7NumericalOwnedTailPolynomialConstant_pos :
    0 < preE7NumericalOwnedTailPolynomialConstant := by
  unfold preE7NumericalOwnedTailPolynomialConstant
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- All ordinary-owner tail coefficients, including bounded-width polynomial
tails, satisfy the common subquadratic/log-squared numerator envelope. -/
theorem preE7NumericalOwned_tail_envelope :
    SubquadraticLinearLogSquaredMenuNumeratorBound 3
      (fun w (a : PreE7NumericalOwnedIndex w) b =>
        (preE7NumericalOwnedPackage a).package.certificate.T b) := by
  intro ε hε
  let K := preE7NumericalOwnedTailPolynomialConstant
  let C : ℝ := 16 + preE7NumericalOwnedTailPolynomialDegree
  have hK0 : 0 ≤ K := preE7NumericalOwnedTailPolynomialConstant_pos.le
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K, 0, C, hK0, by norm_num, hC0, ?_⟩
  intro n w hw a
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
  rcases (preE7NumericalOwnedPackage a).tail_total_growth with hmenu | hpoly
  · have hold := hmenu (n - w)
    have hconst : 1 ≤ K := by
      dsimp [K, preE7NumericalOwnedTailPolynomialConstant]
      exact le_max_left _ _
    have hexp : 16 * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2 ≤
        ε * (w : ℝ) ^ 2 + 0 * w +
          C * w * Real.log ((n : ℝ) + 2) ^ 2 := by
      dsimp [C]
      have hp0 : (0 : ℝ) ≤ preE7NumericalOwnedTailPolynomialDegree := by
        positivity
      nlinarith [mul_nonneg hp0 (mul_nonneg hw0 hlog0),
        mul_nonneg hε.le (sq_nonneg (w : ℝ))]
    calc
      _ ≤ (2 : ℝ) ^
          (16 * (w : ℝ) *
            Real.log ((w + (n - w) + 2 : ℕ) : ℝ) ^ 2) := hold
      _ ≤ K * (2 : ℝ) ^
          (ε * (w : ℝ) ^ 2 + 0 * w +
            C * w * Real.log ((n : ℝ) + 2) ^ 2) := by
        rw [hwb]
        have hpow := Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) hexp
        have hpow' : (2 : ℝ) ^
              (16 * (w : ℝ) * Real.log (((n + 2 : ℕ) : ℝ)) ^ 2) ≤
            (2 : ℝ) ^
              (ε * (w : ℝ) ^ 2 + 0 * w +
                C * w * Real.log ((n : ℝ) + 2) ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using hpow
        exact hpow'.trans (by
          nth_rewrite 1 [← one_mul ((2 : ℝ) ^ _)]
          exact mul_le_mul_of_nonneg_right hconst (by positivity))
  · rcases hpoly with ⟨hw12288, K0, p, hK0', hrow⟩
    let fw : Fin 12289 := ⟨w, by omega⟩
    let z : PreE7BoundedTailNumericalOwnedIndex := ⟨fw, a⟩
    have hzpoly : HasPolynomialTail z := ⟨K0, p, hK0', hrow⟩
    have hconst : boundedTailPolynomialConstant z ≤ K :=
      (boundedTailPolynomialConstant_le_upper z).trans
        (le_max_right 1 boundedTailPolynomialConstantUpper)
    have hdegree : boundedTailPolynomialDegree z ≤
        preE7NumericalOwnedTailPolynomialDegree :=
      boundedTailPolynomialDegree_le_upper z
    have hrowz := boundedTailPolynomialRow z hzpoly (n - w)
    have hbase : (1 : ℝ) ≤ 1 + (n - w : ℕ) :=
      le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hpow : (1 + ((n - w : ℕ) : ℝ)) ^ boundedTailPolynomialDegree z ≤
        (1 + ((n - w : ℕ) : ℝ)) ^ preE7NumericalOwnedTailPolynomialDegree :=
      pow_le_pow_right₀ hbase hdegree
    have hshift := shiftedNatPow_le_widthLogSquared
      preE7NumericalOwnedTailPolynomialDegree n w hw
    have hexp : (preE7NumericalOwnedTailPolynomialDegree : ℝ) * w *
          Real.log ((n : ℝ) + 2) ^ 2 ≤
        ε * (w : ℝ) ^ 2 + 0 * w +
          C * w * Real.log ((n : ℝ) + 2) ^ 2 := by
      dsimp [C]
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 16)
          (mul_nonneg hw0 hlog0),
        mul_nonneg hε.le (sq_nonneg (w : ℝ))]
    calc
      _ ≤ boundedTailPolynomialConstant z *
          (1 + ((n - w : ℕ) : ℝ)) ^ boundedTailPolynomialDegree z := by
        simpa [z] using hrowz
      _ ≤ K * (1 + ((n - w : ℕ) : ℝ)) ^ boundedTailPolynomialDegree z :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ ≤ K * (1 + ((n - w : ℕ) : ℝ)) ^
          preE7NumericalOwnedTailPolynomialDegree :=
        mul_le_mul_of_nonneg_left hpow hK0
      _ ≤ K * (2 : ℝ) ^
          ((preE7NumericalOwnedTailPolynomialDegree : ℝ) * w *
            Real.log ((n : ℝ) + 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hshift hK0
      _ ≤ K * (2 : ℝ) ^
          (ε * (w : ℝ) ^ 2 + 0 * w +
            C * w * Real.log ((n : ℝ) + 2) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hK0

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
