import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource

/-!
# Uniform coefficient bound for a degree-three affine layer

This is the coefficient half of every small signed-quotient endpoint.  It
turns Tracey's explicit one-dimensional ternary layer coefficient into the
common affine width cost, uniformly in the block count and source degree.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A one-dimensional ternary translation-layer coefficient is absorbed by
the standard affine menu mass at physical width `w = 3s`. -/
theorem degreeThreeTranslationCoefficient_bound
    (s w : ℕ) (hs : 2 ≤ s) (hw : w = 3 * s) (C : ℝ)
    (hC : C ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 s
        (traceyInducedGeneratorCeiling 1 s)
        (traceyPermutationGeneratorCeiling w) w 3) :
    ∀ b : ℕ, C ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
  intro b
  let X : ℝ := Real.logb 2 3
  let A : ℕ := traceyAffineCoefficientExponent 1 s
    (traceyInducedGeneratorCeiling 1 s)
    (traceyPermutationGeneratorCeiling w) w 3
  let q : ℝ := Real.sqrt (Real.logb 2 (s : ℝ))
  let B : ℝ := 4 * s * w / q +
    s * (traceyPermutationGeneratorCeiling w + 2) + w
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact Real.logb_nonneg (by norm_num) (by norm_num)
  have hX4 : X ≤ 4 := by
    have hlog2 : Real.logb 2 3 ≤ 2 := by
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
      simpa [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
        Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
    dsimp [X]
    linarith
  have hXsq : X ^ 2 ≤ (4 : ℝ) ^ 2 := by nlinarith
  have hraw := traceyAffineCoefficientExponent_log_le
    1 s (traceyPermutationGeneratorCeiling w) w 3
    (by norm_num) hs
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2
      (Real.logb_pos (by norm_num) (by exact_mod_cast hs))
  have hA0 : 0 ≤ 4 * (s : ℝ) ^ 2 / q := by positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcore : X * (A : ℝ) ≤
      4 * (s : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 := by
    calc
      X * (A : ℝ) ≤
          4 * (s : ℝ) ^ 2 / q * X ^ 2 + B * X := by
        simpa only [X, A, q, B, one_mul, Nat.cast_ofNat,
          Nat.cast_add, Nat.cast_one] using hraw
      _ ≤ 4 * (s : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 :=
        add_le_add (mul_le_mul_of_nonneg_left hXsq hA0)
          (mul_le_mul_of_nonneg_left hX4 hB0)
  have hlogb : 0 ≤ Real.logb 2 (b + 1) :=
    Real.logb_nonneg (by norm_num)
      (by exact_mod_cast (show 1 ≤ b + 1 by omega))
  have hexp : X * (A : ℝ) ≤
      affineComponentCoefficientExponent 3 s w b := by
    calc
      _ ≤ 4 * (s : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 := hcore
      _ ≤ 4 * (s : ℝ) ^ 2 / q * (4 : ℝ) ^ 2 + B * 4 +
          3 * s * 4 + 2 * s * 4 * Real.logb 2 (b + 1) := by
        have htail : 0 ≤ 3 * (s : ℝ) * 4 +
            2 * s * 4 * Real.logb 2 (b + 1) := by positivity
        linarith
      _ = affineComponentCoefficientExponent 3 s w b := by
        norm_num [affineComponentCoefficientExponent, q, B, Nat.log]
  have hpowReal : (3 : ℝ) ^ (A : ℝ) =
      (2 : ℝ) ^ (X * (A : ℝ)) := by
    dsimp [X]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
        (by norm_num) (by norm_num)]
  have hpow : (3 : ℝ) ^ A = (2 : ℝ) ^ (X * (A : ℝ)) := by
    rw [← Real.rpow_natCast (3 : ℝ) A]
    exact hpowReal
  calc
    C ≤ (3 : ℝ) ^ A := by simpa only [A] using hC
    _ = (2 : ℝ) ^ (X * (A : ℝ)) := hpow
    _ ≤ (2 : ℝ) ^ affineComponentCoefficientExponent 3 s w b :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (affineComponentCoefficientExponent_le_widthCost
          3 s w b (by norm_num) hs hw)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
