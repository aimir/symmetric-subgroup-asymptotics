import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalRows
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveMenuGrowth

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

/-- The affine source logarithm fits the common linear/log-squared menu
envelope.  Exported for residual rows carrying the same affine coefficient
shape. -/
theorem affineSourceLog_le_widthLogSquared
    (n w : ℕ) (hw : w ∈ Finset.Ico 3 (n + 1)) :
    8 * (w : ℝ) * Real.logb 2 ((n - w + 1 : ℕ) : ℝ) ≤
      (8 / Real.log 2 ^ 2) * w * Real.log ((n : ℝ) + 2) ^ 2 := by
  have hww := Finset.mem_Ico.mp hw
  have harg : (n - w + 1 : ℕ) ≤ n + 2 := by omega
  have hargpos : (0 : ℝ) < ((n - w + 1 : ℕ) : ℝ) := by positivity
  have hn2pos : (0 : ℝ) < n + 2 := by positivity
  have hargR : (((n - w + 1 : ℕ) : ℝ)) ≤ (((n + 2 : ℕ) : ℝ)) := by
    exact_mod_cast harg
  have hmono0 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    hargpos hargR
  have hmono : Real.logb 2 (((n - w + 1 : ℕ) : ℝ)) ≤
      Real.logb 2 ((n : ℝ) + 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hmono0
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloglower : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast
      (show 2 ≤ n + 2 by omega))
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) :=
    hlog2pos.le.trans hloglower
  have hquot : Real.logb 2 ((n : ℝ) + 2) ≤
      Real.log ((n : ℝ) + 2) ^ 2 / Real.log 2 ^ 2 := by
    rw [Real.logb]
    apply (div_le_div_iff₀ hlog2pos (sq_pos_of_pos hlog2pos)).2
    nlinarith [mul_le_mul_of_nonneg_right hloglower hlog0]
  have hw0 : (0 : ℝ) ≤ w := by positivity
  calc
    _ ≤ 8 * (w : ℝ) * Real.logb 2 ((n : ℝ) + 2) := by gcongr
    _ ≤ 8 * (w : ℝ) *
        (Real.log ((n : ℝ) + 2) ^ 2 / Real.log 2 ^ 2) := by gcongr
    _ = _ := by ring

/-- Every ordinary numerical row, including bounded polynomials and the
actual imprimitive-affine rows, satisfies the combined subquadratic-width
and linear/log-squared envelope. -/
theorem preE7NumericalOwned_main_envelope :
    SubquadraticLinearLogSquaredMenuNumeratorBound 3
      (fun w (a : PreE7NumericalOwnedIndex w) b =>
        (preE7NumericalOwnedPackage a).package.certificate.D b) := by
  intro ε hε
  obtain ⟨Kaff, hKaff1, hAff⟩ :=
    PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost_rpow_envelope hε
  let K := max preE7NumericalOwnedPolynomialConstant Kaff
  let C : ℝ := 16 + preE7NumericalOwnedPolynomialDegree +
    8 / Real.log 2 ^ 2
  have hK0 : 0 ≤ K := by
    exact (le_max_left _ _).trans' preE7NumericalOwnedPolynomialConstant_pos.le
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K, 0, C, hK0, by norm_num, hC0, ?_⟩
  intro n w hw a
  have hwb : w + (n - w) + 2 = n + 2 := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  have hww := Finset.mem_Ico.mp hw
  have hw0 : (0 : ℝ) ≤ w := by positivity
  have hw1 : 1 ≤ w := by omega
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
  rcases (preE7NumericalOwnedPackage a).main_total_growth with hmain | hrest
  · have hold := hmain (n - w)
    have hconst : 1 ≤ K :=
      (show 1 ≤ preE7NumericalOwnedPolynomialConstant by
        unfold preE7NumericalOwnedPolynomialConstant
        exact le_max_left _ _).trans (le_max_left _ _)
    calc
      _ ≤ (2 : ℝ) ^
          (16 * (w : ℝ) *
            Real.log ((w + (n - w) + 2 : ℕ) : ℝ) ^ 2) := hold
      _ ≤ K * (2 : ℝ) ^
          (ε * (w : ℝ) ^ 2 + 0 * w +
            C * w * Real.log ((n : ℝ) + 2) ^ 2) := by
        rw [hwb]
        have hexp : 16 * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2 ≤
            ε * (w : ℝ) ^ 2 + 0 * w +
              C * w * Real.log ((n : ℝ) + 2) ^ 2 := by
          dsimp [C]
          have hp0 : (0 : ℝ) ≤ preE7NumericalOwnedPolynomialDegree := by positivity
          have ha0 : 0 ≤ 8 / Real.log 2 ^ 2 := by positivity
          nlinarith [mul_nonneg (add_nonneg hp0 ha0) (mul_nonneg hw0 hlog0),
            mul_nonneg hε.le (sq_nonneg (w : ℝ))]
        have hpow : (2 : ℝ) ^
              (16 * (w : ℝ) * Real.log ((n : ℝ) + 2) ^ 2) ≤
            (2 : ℝ) ^
              (ε * (w : ℝ) ^ 2 + 0 * w +
                C * w * Real.log ((n : ℝ) + 2) ^ 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hpow.trans (by
          nth_rewrite 1 [← one_mul ((2 : ℝ) ^ _)]
          exact mul_le_mul_of_nonneg_right hconst (by positivity))
  · rcases hrest with hpoly | haffine
    · rcases hpoly with ⟨hw1024, K0, p, hK0', hrow⟩
      let fw : Fin 1025 := ⟨w, by omega⟩
      let z : PreE7BoundedNumericalOwnedIndex := ⟨fw, a⟩
      have hzpoly : HasPolynomialRow z := ⟨K0, p, hK0', hrow⟩
      have hconst : boundedPolynomialConstant z ≤ K :=
        (boundedPolynomialConstant_le_upper z).trans
          ((le_max_right 1 boundedPolynomialConstantUpper).trans
            (le_max_left _ Kaff))
      have hdegree : boundedPolynomialDegree z ≤
          preE7NumericalOwnedPolynomialDegree :=
        boundedPolynomialDegree_le_upper z
      have hrowz := boundedPolynomialRow z hzpoly (n - w)
      have hbase : (1 : ℝ) ≤ 1 + (n - w : ℕ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg _)
      have hpow : (1 + ((n - w : ℕ) : ℝ)) ^ boundedPolynomialDegree z ≤
          (1 + ((n - w : ℕ) : ℝ)) ^ preE7NumericalOwnedPolynomialDegree :=
        pow_le_pow_right₀ hbase hdegree
      have hshift := shiftedNatPow_le_widthLogSquared
        preE7NumericalOwnedPolynomialDegree n w hw
      have hexp : (preE7NumericalOwnedPolynomialDegree : ℝ) * w *
            Real.log ((n : ℝ) + 2) ^ 2 ≤
          ε * (w : ℝ) ^ 2 + 0 * w +
            C * w * Real.log ((n : ℝ) + 2) ^ 2 := by
        dsimp [C]
        have h16 : (0 : ℝ) ≤ 16 := by norm_num
        have ha0 : 0 ≤ 8 / Real.log 2 ^ 2 := by positivity
        nlinarith [mul_nonneg (add_nonneg h16 ha0) (mul_nonneg hw0 hlog0),
          mul_nonneg hε.le (sq_nonneg (w : ℝ))]
      calc
        _ ≤ boundedPolynomialConstant z *
            (1 + ((n - w : ℕ) : ℝ)) ^ boundedPolynomialDegree z := by
          simpa [z] using hrowz
        _ ≤ K * (1 + ((n - w : ℕ) : ℝ)) ^ boundedPolynomialDegree z :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
        _ ≤ K * (1 + ((n - w : ℕ) : ℝ)) ^
            preE7NumericalOwnedPolynomialDegree :=
          mul_le_mul_of_nonneg_left hpow hK0
        _ ≤ K * (2 : ℝ) ^
            ((preE7NumericalOwnedPolynomialDegree : ℝ) * w *
              Real.log ((n : ℝ) + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hshift hK0
        _ ≤ K * (2 : ℝ) ^
            (ε * (w : ℝ) ^ 2 + 0 * w +
              C * w * Real.log ((n : ℝ) + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hK0
    · have hold := haffine (n - w)
      have hcost := hAff w hw1
      have hsource := affineSourceLog_le_widthLogSquared n w hw
      have hKaff : Kaff ≤ K := le_max_right _ _
      have hCsrc : (8 / Real.log 2 ^ 2) * w *
            Real.log ((n : ℝ) + 2) ^ 2 ≤
          C * w * Real.log ((n : ℝ) + 2) ^ 2 := by
        dsimp [C]
        have hnon : 0 ≤ (16 + (preE7NumericalOwnedPolynomialDegree : ℝ)) := by
          positivity
        nlinarith [mul_nonneg hnon (mul_nonneg hw0 hlog0)]
      calc
        _ ≤ (2 : ℝ) ^
            (PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w +
              8 * (w : ℝ) * Real.logb 2 ((n - w + 1 : ℕ) : ℝ)) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hold
        _ = (2 : ℝ) ^
            PrimitiveAffineImprimitiveBlockTransfer.affineComponentWidthCost w *
            (2 : ℝ) ^ (8 * (w : ℝ) * Real.logb 2 ((n - w + 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ ≤ (Kaff * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)) *
            (2 : ℝ) ^ ((8 / Real.log 2 ^ 2) * w *
              Real.log ((n : ℝ) + 2) ^ 2) :=
          mul_le_mul hcost
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hsource)
            (by positivity) (by positivity)
        _ ≤ (K * (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)) *
            (2 : ℝ) ^ (C * w * Real.log ((n : ℝ) + 2) ^ 2) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right hKaff (by positivity))
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) hCsrc)
            (by positivity) (by positivity)
        _ = K * (2 : ℝ) ^
            (ε * (w : ℝ) ^ 2 + 0 * w +
              C * w * Real.log ((n : ℝ) + 2) ^ 2) := by
          calc
            _ = K * ((2 : ℝ) ^ (ε * (w : ℝ) ^ 2) *
                (2 : ℝ) ^ (C * w * Real.log ((n : ℝ) + 2) ^ 2)) := by ring
            _ = K * (2 : ℝ) ^
                (ε * (w : ℝ) ^ 2 +
                  C * w * Real.log ((n : ℝ) + 2) ^ 2) := by
              rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            _ = _ := by congr 2 <;> ring

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
