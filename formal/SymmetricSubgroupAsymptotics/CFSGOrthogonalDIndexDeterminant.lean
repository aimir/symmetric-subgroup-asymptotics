import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The SAME elementary D action has determinant one over every field.
This is proved on its literal root arrays, not inferred from an
identification with an abstract orthogonal or special orthogonal group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexDeterminant
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationInitialElements CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationPureRootCoverage
variable (K : Type) [Field K]

private theorem det_paired {I : Type} [Fintype I] [DecidableEq I]
    (a b c d : I) (hab : a ≠ b) (hcd : c ≠ d) (hbc : b ≠ c) (t : K) :
    Matrix.det (1 + Matrix.single a b t - Matrix.single c d t) = 1 := by
  have he : (1 + Matrix.single a b t - Matrix.single c d t : Matrix I I K) =
      Matrix.transvection a b t * Matrix.transvection c d (-t) := by
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one,
      Matrix.single_mul_single_of_ne _ _ _ _ hbc]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Pi.zero_apply,
      add_zero]
    split_ifs <;> ring
  rw [he, Matrix.det_mul, Matrix.det_transvection_of_ne a b hab,
    Matrix.det_transvection_of_ne c d hcd, one_mul]

theorem chainArray_det {r : ℕ} (i j : Fin r) (hij : i ≠ j) (a : K) :
    Matrix.det (chainArray i j a) = 1 := by
  exact det_paired K (Sum.inl i) (Sum.inl j) (Sum.inr j) (Sum.inr i)
    (fun h => hij (Sum.inl.inj h)) (fun h => hij (Sum.inr.inj h).symm)
    (by simp) a

theorem plusArray_det {r : ℕ} (i j : Fin r) (a : K) :
    Matrix.det (plusArray i j a) = 1 := by
  exact det_paired K (Sum.inl i) (Sum.inr j) (Sum.inl j) (Sum.inr i)
    (by simp) (by simp) (by simp) a

theorem minusArray_det {r : ℕ} (i j : Fin r) (a : K) :
    Matrix.det (minusArray i j a) = 1 := by
  rw [minusArray, Matrix.det_transpose]
  exact plusArray_det K i j a

theorem root_det (s : ℕ) (neg : Bool) (i : Fin (s + 4)) (a : K) :
    Matrix.det (rootTransvection K (s + 4) neg i a : Mat K (s + 4)) = 1 := by
  by_cases hi : i.val + 1 < s + 4
  · have hij : i ≠ (⟨i.val + 1, hi⟩ : Fin (s + 4)) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val + 1 at hv
      omega
    change Matrix.det ((rootElement K (s + 4) neg i a).val : Mat K (s + 4)) = 1
    rw [chain_root_array K s neg i hi a]
    cases neg
    · exact chainArray_det K i _ hij a
    · exact chainArray_det K _ i (Ne.symm hij) a
  · have he : i = last (s + 2) := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = s + 3
      omega
    subst i
    change Matrix.det ((rootElement K (s + 4) neg (last (s + 2)) a).val : Mat K (s + 4)) = 1
    rw [forkRoot_coe K s neg a]
    cases neg
    · exact plusArray_det K (pen (s + 2)) (last (s + 2)) a
    · simpa only [if_true, minusArray, plusArray, Matrix.transpose_add,
        Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_single] using
        minusArray_det K (pen (s + 2)) (last (s + 2)) a

theorem elementary_det (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    Matrix.det (g.val : Mat K (s + 4)) = 1 := by
  let H : Subgroup (Mat K (s + 4))ˣ :=
    (Matrix.GeneralLinearGroup.det : (Mat K (s + 4))ˣ →* Kˣ).ker
  have hle : elementaryRootGroup K (s + 4) ≤ H := by
    apply (Subgroup.closure_le H).mpr
    rintro u ⟨neg, i, a, rfl⟩
    change Matrix.GeneralLinearGroup.det (rootTransvection K (s + 4) neg i a) = 1
    apply Units.ext
    exact root_det K s neg i a
  have he : Matrix.GeneralLinearGroup.det g.val = 1 := hle g.property
  exact congrArg (fun u : Kˣ => (u : K)) he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexDeterminant
