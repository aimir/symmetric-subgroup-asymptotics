import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexComponentMatrices
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveInvariant

/-! Every literal D root lies in the genuine even-component subgroup.
Chain and positive-fork roots fix the original positive space. The
negative fork is a lower shear, whose intersection parity follows from
the actual alternating form of its shear matrix. This works also in
characteristic two, without assuming an orthogonal component theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDGenerationInitialRootMatrices CFSGOrthogonalDGenerationPureRootCoverage
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexComponentMatrices CFSGOrthogonalDIndexPositiveInvariant
open CFSGOrthogonalDIndexSingularComponents CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem minusArray_eq_lower {r : ℕ} (i j : Fin r) (a : K) :
    minusArray i j a =
      ((lower (Matrix.single j i a - Matrix.single i j a)) : Mat K r) := by
  ext x y
  cases x <;> cases y <;>
    simp [minusArray, plusArray, lower, Matrix.single_apply, Matrix.one_apply,
      eq_comm, and_comm]

theorem root_mem_componentMatrices (s : ℕ) (neg : Bool) (i : Fin (s + 4)) (a : K) :
    rootTransvection K (s + 4) neg i a ∈ componentMatrices K (s + 4) := by
  let g := rootTransvection K (s + 4) neg i a
  have hQ : ∀ x, splitQuadraticForm K (s + 4)
      (ambientLinearEquiv K (s + 4) g x) = splitQuadraticForm K (s + 4) x := by
    intro x
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
    exact root_preserves_splitQ K s neg i a x
  by_cases hi : i.val + 1 < s + 4
  · apply mem_componentMatrices_of_positive_fixed K (s + 4) g hQ
    apply positive_fixed_of_lower_left_zero
    intro j k
    change ((rootElement K (s + 4) neg i a).val : Mat K (s + 4))
      (Sum.inr j) (Sum.inl k) = 0
    rw [chain_root_array K s neg i hi a]
    cases neg <;> simp [chainArray]
  · have he : i = last (s + 2) := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = s + 3
      omega
    subst i
    cases neg with
    | false =>
      apply mem_componentMatrices_of_positive_fixed K (s + 4) g hQ
      apply positive_fixed_of_lower_left_zero
      intro j k
      change ((rootElement K (s + 4) false (last (s + 2)) a).val : Mat K (s + 4))
        (Sum.inr j) (Sum.inl k) = 0
      rw [forkRoot_coe K s false a]
      simp
    | true =>
      have hg : g = lower (Matrix.single (last (s + 2)) (pen (s + 2)) a -
          Matrix.single (pen (s + 2)) (last (s + 2)) a) := by
        apply Units.ext
        change ((rootElement K (s + 4) true (last (s + 2)) a).val : Mat K (s + 4)) = _
        rw [forkRoot_coe K s true a]
        simpa only [minusArray, plusArray, Matrix.transpose_add, Matrix.transpose_sub,
          Matrix.transpose_one, Matrix.transpose_single] using
          minusArray_eq_lower K (pen (s + 2)) (last (s + 2)) a
      change g ∈ componentMatrices K (s + 4)
      rw [hg] at hQ ⊢
      exact lower_mem_componentMatrices K (s + 4) _ hQ

theorem elementary_le_componentMatrices (s : ℕ) :
    elementaryRootGroup K (s + 4) ≤ componentMatrices K (s + 4) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg, i, a, rfl⟩
  exact root_mem_componentMatrices K s neg i a

theorem elementary_even_distance (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    Even (distance (s + 4) (positiveSpace K (s + 4))
      ((positiveSpace K (s + 4)).map (naturalLinearHom K (s + 4) g).toLinearMap)) := by
  exact ((mem_componentMatrices_iff K (s + 4) g.val).mp
    (elementary_le_componentMatrices K s g.property)).2

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents
