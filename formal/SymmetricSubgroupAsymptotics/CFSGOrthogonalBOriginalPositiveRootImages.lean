import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootParents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformRootMatrixArithmetic

/-! Literal positive root images of paths in the SAME original integral
B source. Induction uses checked original-source parent equalities and
uniform sparse matrix arithmetic, never realization injectivity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveRootImages
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBOriginalRootParents
variable (r : ℕ)

theorem generator_E_image (i : Fin r) :
    integralOrthogonalRepresentation r
      (latticeGenerator (CartanMatrix.B r).transpose (.E i)) = positive ℤ r i :=
  CFSGSerreQuadraticMatrix.integralRepresentation_generator (realizationData r) (.E i)

theorem short_image (i : Fin r) :
    integralOrthogonalRepresentation r (CFSGOrthogonalBOriginalRootCandidates.short r false i) =
      CFSGOrthogonalBUniformRootMatrixArithmetic.short ℤ r i := by
  suffices h : ∀ n : ℕ, ∀ i : Fin r, r - i.val = n →
      integralOrthogonalRepresentation r (CFSGOrthogonalBOriginalRootCandidates.short r false i) =
        CFSGOrthogonalBUniformRootMatrixArithmetic.short ℤ r i by
    exact h _ i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hn
    by_cases hi : i.val + 1 < r
    · have hp := positive_short_parent r i hi
      dsimp only at hp
      rw [← hp, CFSGSerreQuadraticMatrix.integralRepresentation_operator,
        ih (r - (i.val + 1)) (by omega) ⟨i.val + 1, hi⟩ rfl]
      change CFSGIntegralQuadraticRootOperators.operator ℤ (positive ℤ r i)
        (positiveSecond ℤ r i) 1
        (CFSGOrthogonalBUniformRootMatrixArithmetic.short ℤ r ⟨i.val + 1, hi⟩) = _
      rw [CFSGIntegralQuadraticRootOperators.operator_one]
      exact CFSGOrthogonalBUniformRootMatrixArithmetic.short_parent ℤ r i hi
    · have he : (⟨r - 1, by have hlt := i.isLt; omega⟩ : Fin r) = i := by
        apply Fin.ext
        change r - 1 = i.val
        have hlt := i.isLt
        omega
      simp only [CFSGOrthogonalBOriginalRootCandidates.short, he, descend_self,
        steps, List.map_nil, path, Bool.false_eq_true, if_false, one_smul,
        CFSGSerreDividedPowerPaths.pathVector, CFSGSerreDividedPowerPaths.applySteps]
      rw [generator_E_image]
      simp only [positive, dif_neg hi, CFSGOrthogonalBUniformRootMatrixArithmetic.short]

theorem difference_image (ij : Pair r) :
    integralOrthogonalRepresentation r
      (CFSGOrthogonalBOriginalRootCandidates.difference r false ij) =
      CFSGOrthogonalBUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2 := by
  suffices h : ∀ n : ℕ, ∀ ij : Pair r, ij.val.2.val - ij.val.1.val = n →
      integralOrthogonalRepresentation r
        (CFSGOrthogonalBOriginalRootCandidates.difference r false ij) =
        CFSGOrthogonalBUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2 by
    exact h _ ij rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ij hn
    let i := ij.val.1
    let j := ij.val.2
    have hij : i.val < j.val := ij.property
    have hi : i.val + 1 < r := by have hj := j.isLt; omega
    by_cases hadj : j.val = i.val + 1
    · have hstart : (⟨j.val - 1, by have hjlt := j.isLt; omega⟩ : Fin r) = i := by
        apply Fin.ext
        change j.val - 1 = i.val
        omega
      unfold CFSGOrthogonalBOriginalRootCandidates.difference
      change integralOrthogonalRepresentation r (path r false _ _) = _
      rw [hstart, descend_self]
      simp only [steps, List.map_nil, path, Bool.false_eq_true, if_false, one_smul,
        CFSGSerreDividedPowerPaths.pathVector, CFSGSerreDividedPowerPaths.applySteps]
      rw [generator_E_image]
      have hj : (⟨i.val + 1, hi⟩ : Fin r) = j := Fin.ext hadj.symm
      simp only [positive, dif_pos hi, hj,
        CFSGOrthogonalBUniformRootMatrixArithmetic.difference] <;> rfl
    · have hgap : i.val + 1 < j.val := by omega
      let next : Fin r := ⟨i.val + 1, hi⟩
      let parent : Pair r := ⟨(next, j), hgap⟩
      have hp := positive_difference_parent r i j hgap
      change integralOperator _ false i 1
        (CFSGOrthogonalBOriginalRootCandidates.difference r false parent) =
          CFSGOrthogonalBOriginalRootCandidates.difference r false ij at hp
      rw [← hp, CFSGSerreQuadraticMatrix.integralRepresentation_operator,
        ih (j.val - next.val) (by dsimp [next]; omega) parent rfl]
      change CFSGIntegralQuadraticRootOperators.operator ℤ (positive ℤ r i)
        (positiveSecond ℤ r i) 1
        (CFSGOrthogonalBUniformRootMatrixArithmetic.difference ℤ r next j) = _
      rw [CFSGIntegralQuadraticRootOperators.operator_one]
      exact CFSGOrthogonalBUniformRootMatrixArithmetic.difference_parent ℤ r i j hi hgap

theorem matrixSteps_append (neg : Bool) (ss tt : List (Fin r × ℕ)) (x : Mat ℤ r) :
    matrixSteps r neg (ss ++ tt) x = matrixSteps r neg tt (matrixSteps r neg ss x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveRootImages
