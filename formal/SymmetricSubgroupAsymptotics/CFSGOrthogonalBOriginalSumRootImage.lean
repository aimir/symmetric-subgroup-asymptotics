import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveRootImages

/-! The remaining positive sum-root image is computed from the SAME
original path: a terminal second divided power, then descent of the
second index. No source equality is inferred from matrix equality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalSumRootImage
open CFSG.Models.Chevalley CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBOriginalRootParents
open CFSGOrthogonalBOriginalPositiveRootImages
variable (r : ℕ)

theorem matrixSteps_neg (neg : Bool) (ss : List (Fin r × ℕ)) (x : Mat ℤ r) :
    matrixSteps r neg ss (-x) = -matrixSteps r neg ss x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    change matrixSteps r neg ss
      (CFSGIntegralQuadraticRootOperators.operator ℤ (rootMatrix ℤ r neg s.1)
        (rootSecond ℤ r neg s.1) s.2 (-x)) =
      -matrixSteps r neg ss
        (CFSGIntegralQuadraticRootOperators.operator ℤ (rootMatrix ℤ r neg s.1)
          (rootSecond ℤ r neg s.1) s.2 x)
    rw [map_neg, ih]

theorem sum_descent (i last j : Fin r) (hij : i.val < j.val)
    (hjlast : j.val ≤ last.val) :
    matrixSteps r false (steps r (descend r j last) 1)
      (CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot ℤ r i last) =
        CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot ℤ r i j := by
  suffices h : ∀ n : ℕ, ∀ j : Fin r, i.val < j.val → j.val ≤ last.val →
      last.val - j.val = n →
      matrixSteps r false (steps r (descend r j last) 1)
        (CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot ℤ r i last) =
          CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot ℤ r i j by
    exact h _ j hij hjlast rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro j hij hjlast hn
    by_cases he : j = last
    · subst j
      simp only [descend_self, steps, List.map_nil, matrixSteps]
    · have hjlt : j.val < last.val := by
        have hne : j.val ≠ last.val := fun hv => he (Fin.ext hv)
        omega
      have hj : j.val + 1 < r := by have hlast := last.isLt; omega
      let next : Fin r := ⟨j.val + 1, hj⟩
      rw [descend_split r j last hjlt]
      simp only [steps, List.map_append, List.map_cons, List.map_nil]
      rw [matrixSteps_append]
      change matrixSteps r false [(j, 1)]
        (matrixSteps r false (steps r (descend r next last) 1)
          (CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot ℤ r i last)) = _
      rw [ih (last.val - next.val) (by dsimp [next]; omega) next
        (by dsimp [next]; omega) (by dsimp [next]; omega) rfl]
      change CFSGIntegralQuadraticRootOperators.operator ℤ (positive ℤ r j)
        (positiveSecond ℤ r j) 1
        (CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot ℤ r i next) = _
      rw [CFSGIntegralQuadraticRootOperators.operator_one]
      exact CFSGOrthogonalBUniformRootMatrixArithmetic.sum_second_parent ℤ r i j hj hij

theorem sum_image (ij : Pair r) :
    integralOrthogonalRepresentation r
      (CFSGOrthogonalBOriginalRootCandidates.sumRoot r false ij) =
        CFSGOrthogonalBUniformRootMatrixArithmetic.sumRoot ℤ r ij.val.1 ij.val.2 := by
  let i := ij.val.1
  let j := ij.val.2
  have hij : i.val < j.val := ij.property
  let last : Fin r := ⟨r - 1, by have hj := j.isLt; omega⟩
  let previous : Fin r := ⟨r - 2, by have hj := j.isLt; omega⟩
  have hilast : i.val < last.val := by
    have hj := j.isLt
    dsimp [last]
    omega
  let ilast : Pair r := ⟨(i, last), hilast⟩
  have hprevious : (⟨last.val - 1, by have hl := last.isLt; omega⟩ : Fin r) = previous := by
    apply Fin.ext
    dsimp [last, previous]
    omega
  have hd := difference_image r ilast
  change integralOrthogonalRepresentation r
    (path r false ⟨last.val - 1, by have hl := last.isLt; omega⟩
      (steps r (descend r i ⟨last.val - 1, by have hl := last.isLt; omega⟩) 1)) = _ at hd
  rw [hprevious, path_image] at hd
  simp only [Bool.false_eq_true, if_false, one_smul, integerGenerator] at hd
  change matrixSteps r false (steps r (descend r i previous) 1)
    (positive ℤ r previous) =
      CFSGOrthogonalBUniformRootMatrixArithmetic.difference ℤ r i last at hd
  change integralOrthogonalRepresentation r
    ((-1 : ℤ) • path r false previous
      (steps r (descend r i previous) 1 ++ [(last, 2)] ++
        steps r (descend r j last) 1)) = _
  rw [map_smul, path_image]
  simp only [Bool.false_eq_true, if_false, one_smul, integerGenerator]
  rw [matrixSteps_append, matrixSteps_append, hd]
  change (-1 : ℤ) • matrixSteps r false (steps r (descend r j last) 1)
    (CFSGIntegralQuadraticRootOperators.operator ℤ (positive ℤ r last)
      (positiveSecond ℤ r last) 2
      (CFSGOrthogonalBUniformRootMatrixArithmetic.difference ℤ r i last)) = _
  rw [CFSGOrthogonalBUniformRootMatrixArithmetic.terminal_second_difference ℤ r i last
    (by dsimp [last]; have hj := j.isLt; omega)
    (by intro h; have hv := congrArg Fin.val h; omega)]
  simp only [matrixSteps_neg, neg_one_smul, neg_neg]
  exact sum_descent r i last j hij (by dsimp [last]; have hj := j.isLt; omega)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalSumRootImage
