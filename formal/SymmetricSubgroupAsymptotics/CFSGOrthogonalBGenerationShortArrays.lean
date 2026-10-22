import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements

/-! Uniform signed-coordinate short-root units. These literal quadratic
arrays will be transported from the terminal original B roots by actual
SL-chain words; no membership is asserted merely from their shape. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortArrays
open Matrix CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K] (r : ℕ)

def paired : Fin r ⊕ Fin r → Fin r ⊕ Fin r := Sum.swap

@[simp] theorem paired_paired (b : Fin r ⊕ Fin r) : paired r (paired r b) = b := by
  cases b <;> rfl

theorem paired_ne (b : Fin r ⊕ Fin r) : paired r b ≠ b := by cases b <;> simp [paired]

def shortArray (b : Fin r ⊕ Fin r) : Mat K r :=
  Matrix.single (Sum.inl b) (middle r) 1 -
    Matrix.single (middle r) (Sum.inl (paired r b)) 2

def shortSecond (b : Fin r ⊕ Fin r) : Mat K r :=
  Matrix.single (Sum.inl b) (Sum.inl (paired r b)) (-1)

theorem short_square (b : Fin r ⊕ Fin r) :
    shortArray K r b * shortArray K r b = shortSecond K r b + shortSecond K r b := by
  simp only [shortArray, shortSecond, sub_mul, mul_sub]
  simp [middle, paired_ne, (paired_ne r b).symm]
  all_goals ext i j
  all_goals simp [Matrix.single]
  all_goals try split_ifs
  all_goals ring

theorem short_mul_second (b : Fin r ⊕ Fin r) :
    shortArray K r b * shortSecond K r b = 0 := by
  simp [shortArray, shortSecond, sub_mul, middle, paired_ne]

theorem second_mul_short (b : Fin r ⊕ Fin r) :
    shortSecond K r b * shortArray K r b = 0 := by
  simp [shortArray, shortSecond, mul_sub, middle, paired_ne]

theorem second_square (b : Fin r ⊕ Fin r) :
    shortSecond K r b * shortSecond K r b = 0 := by
  simp [shortSecond, paired_ne]

def shortUnit (b : Fin r ⊕ Fin r) (a : K) : (Mat K r)ˣ :=
  CFSGQuadraticRootExponential.rootUnit (shortArray K r b) (shortSecond K r b)
    (short_square K r b) (short_mul_second K r b) (second_mul_short K r b)
    (second_square K r b) a

@[simp] theorem shortUnit_val (b : Fin r ⊕ Fin r) (a : K) :
    (shortUnit K r b a : Mat K r) = 1 + a • shortArray K r b + a ^ 2 • shortSecond K r b := rfl

theorem shortUnit_inv_val (b : Fin r ⊕ Fin r) (a : K) :
    (↑((shortUnit K r b a)⁻¹) : Mat K r) =
      1 - a • shortArray K r b + a ^ 2 • shortSecond K r b :=
  CFSGQuadraticRootExponential.rootUnit_inv_val _ _ _ _ _ _ a

@[simp] theorem shortUnit_zero (b : Fin r ⊕ Fin r) : shortUnit K r b 0 = 1 := by
  apply Units.ext
  simp

theorem shortUnit_add (b : Fin r ⊕ Fin r) (a c : K) :
    shortUnit K r b (a + c) = shortUnit K r b a * shortUnit K r b c := by
  apply Units.ext
  change 1 + (a + c) • shortArray K r b + (a + c) ^ 2 • shortSecond K r b =
    (1 + a • shortArray K r b + a ^ 2 • shortSecond K r b) *
      (1 + c • shortArray K r b + c ^ 2 • shortSecond K r b)
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, short_square, short_mul_second, second_mul_short,
    second_square, smul_zero, add_zero, smul_add]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem shortUnit_inv (b : Fin r ⊕ Fin r) (a : K) :
    (shortUnit K r b a)⁻¹ = shortUnit K r b (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← shortUnit_add, add_neg_cancel, shortUnit_zero]

theorem terminal_positive (i : Fin r) (hi : ¬ i.val + 1 < r) (a : K) :
    rootTransvection K r false i a = shortUnit K r (Sum.inl i) a := by
  apply Units.ext
  simp only [rootTransvection_val, shortUnit_val, rootMatrix, rootSecond,
    Bool.false_eq_true, if_false, positive, positiveSecond, dif_neg hi, if_neg hi]
  rfl

theorem terminal_negative (i : Fin r) (hi : ¬ i.val + 1 < r) (a : K) :
    rootTransvection K r true i a = shortUnit K r (Sum.inr i) (-a) := by
  apply Units.ext
  simp only [rootTransvection_val, shortUnit_val, rootMatrix, rootSecond,
    if_true, negative, negativeSecond, dif_neg hi, if_neg hi, neg_sq]
  ext x y
  simp [shortArray, shortSecond, paired, pos, CFSGOrthogonalBSerreMatrices.neg,
    middle, Matrix.single]
  all_goals try split_ifs
  all_goals ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortArrays
