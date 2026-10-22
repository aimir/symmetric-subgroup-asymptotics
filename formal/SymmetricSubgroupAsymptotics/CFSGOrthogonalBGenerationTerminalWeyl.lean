import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationElements

/-! The actual terminal B Weyl word. Its three-dimensional block
interchanges the paired coordinates with minus signs and negates the
middle coordinate, rather than using a type-C coordinate rotation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTerminalWeyl
open Matrix CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationElements
variable (K : Type) [Field K]

def terminalWeyl (r : ℕ) : elementaryRootGroup K (r + 1) :=
  rootElement K (r + 1) false (Fin.last r) (-1) *
    rootElement K (r + 1) true (Fin.last r) 1 *
    rootElement K (r + 1) false (Fin.last r) (-1)

def terminalArray (r : ℕ) : Mat K (r + 1) :=
  1 - Matrix.single (pos (r + 1) (Fin.last r)) (pos (r + 1) (Fin.last r)) 1 -
    Matrix.single (neg (r + 1) (Fin.last r)) (neg (r + 1) (Fin.last r)) 1 -
    Matrix.single (middle (r + 1)) (middle (r + 1)) 2 -
    Matrix.single (pos (r + 1) (Fin.last r)) (neg (r + 1) (Fin.last r)) 1 -
    Matrix.single (neg (r + 1) (Fin.last r)) (pos (r + 1) (Fin.last r)) 1

set_option maxHeartbeats 600000 in
private theorem terminalArray_word (r : ℕ) :
    (1 - positive K (r + 1) (Fin.last r) + positiveSecond K (r + 1) (Fin.last r)) *
      (1 + negative K (r + 1) (Fin.last r) + negativeSecond K (r + 1) (Fin.last r)) *
      (1 - positive K (r + 1) (Fin.last r) + positiveSecond K (r + 1) (Fin.last r)) =
      terminalArray K r := by
  have hi : ¬ (Fin.last r).val + 1 < r + 1 := by simp
  simp [positive, negative,
    positiveSecond, negativeSecond, hi, terminalArray, pos,
    CFSGOrthogonalBSerreMatrices.neg, middle, mul_add, add_mul, mul_sub, sub_mul]
  all_goals ext i j
  all_goals simp [Matrix.single]
  all_goals try split_ifs
  all_goals ring

theorem terminalWeyl_val (r : ℕ) :
    ((terminalWeyl K r).val : Mat K (r + 1)) = terminalArray K r := by
  have hp : ((rootElement K (r + 1) false (Fin.last r) (-1)).val : Mat K (r + 1)) =
      1 - positive K (r + 1) (Fin.last r) + positiveSecond K (r + 1) (Fin.last r) := by
    change (rootTransvection K (r + 1) false (Fin.last r) (-1) : Mat K (r + 1)) = _
    simp only [rootTransvection_val, rootMatrix, rootSecond, Bool.false_eq_true,
      if_false, neg_one_smul, neg_sq, one_pow, one_smul, sub_eq_add_neg]
  have hn : ((rootElement K (r + 1) true (Fin.last r) 1).val : Mat K (r + 1)) =
      1 + negative K (r + 1) (Fin.last r) + negativeSecond K (r + 1) (Fin.last r) := by
    change (rootTransvection K (r + 1) true (Fin.last r) 1 : Mat K (r + 1)) = _
    simp only [rootTransvection_val, rootMatrix, rootSecond, if_true, one_pow, one_smul]
  simp only [terminalWeyl, Subgroup.coe_mul, Units.val_mul, hp, hn]
  exact terminalArray_word K r

theorem terminalWeyl_square (r : ℕ) : terminalWeyl K r ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((terminalWeyl K r).val : Mat K (r + 1)) ^ 2 = 1
  rw [terminalWeyl_val, pow_two]
  simp [terminalArray, pos, CFSGOrthogonalBSerreMatrices.neg, middle,
    mul_add, add_mul, mul_sub, sub_mul]
  all_goals ext i j
  all_goals simp [Matrix.single, Matrix.one_apply]
  all_goals try split_ifs
  all_goals ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTerminalWeyl
