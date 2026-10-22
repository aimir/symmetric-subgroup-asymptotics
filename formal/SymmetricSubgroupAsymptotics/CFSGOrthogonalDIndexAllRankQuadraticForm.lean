import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankRootLines
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm

/-! Original split-Q preservation in every actual D tail of rank>=2.
The same literal simple-root matrices are used; this supplies the low
tail geometry without a named D2/D3 group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankQuadraticForm
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGOrthogonalDIndexAllRankRootLines CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

theorem chain_root_array {r : ℕ} (neg : Bool) (i : Fin r) (hi : i.val + 1 < r) (a : K) :
    (rootTransvection K r neg i a : Mat K r) =
      if neg then chainArray (⟨i.val + 1, hi⟩ : Fin r) i a
      else chainArray i (⟨i.val + 1, hi⟩ : Fin r) a := by
  cases neg <;>
    change 1 + a • rootMatrix K r _ i = _ <;>
    simp only [rootMatrix, Bool.false_eq_true, if_false, if_true, negative,
      positive, dif_pos hi, Matrix.transpose_sub, Matrix.transpose_single,
      smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, chainArray] <;> abel

theorem negative_terminal_root_array (r : ℕ) (hr : 2 ≤ r) (a : K) :
    (rootTransvection K r true (⟨r - 1, by omega⟩ : Fin r) a : Mat K r) =
      minusArray (⟨r - 2, by omega⟩ : Fin r) (⟨r - 1, by omega⟩ : Fin r) a := by
  have h := congrArg Matrix.transpose (terminal_root_array K r hr a)
  change (1 + a • positive K r (⟨r - 1, by omega⟩ : Fin r)).transpose = _ at h
  change 1 + a • (positive K r (⟨r - 1, by omega⟩ : Fin r)).transpose = _
  simpa only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul] using h

theorem root_preserves_splitQ_all_ranks (r : ℕ) (hr : 2 ≤ r)
    (neg : Bool) (i : Fin r) (a : K) (x : Index r → K) :
    splitQ K ((rootTransvection K r neg i a : Mat K r) *ᵥ x) = splitQ K x := by
  by_cases hi : i.val + 1 < r
  · have hij : i ≠ (⟨i.val + 1, hi⟩ : Fin r) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val + 1 at hv
      omega
    rw [chain_root_array K neg i hi a]
    cases neg
    · exact chain_preserves_splitQ K i _ hij a x
    · exact chain_preserves_splitQ K _ i (Ne.symm hij) a x
  · have he : i = (⟨r - 1, by omega⟩ : Fin r) := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = r - 1
      omega
    rw [he]
    cases neg
    · rw [terminal_root_array K r hr a]
      exact plus_preserves_splitQ K _ _ a x
    · rw [negative_terminal_root_array K r hr a]
      exact minus_preserves_splitQ K _ _ a x

theorem elementary_preserves_splitQ_all_ranks (r : ℕ) (hr : 2 ≤ r)
    (g : elementaryRootGroup K r) (x : Index r → K) :
    splitQ K ((g.val : Mat K r) *ᵥ x) = splitQ K x := by
  have hle : elementaryRootGroup K r ≤ quadraticPreserving K r := by
    apply (Subgroup.closure_le _).mpr
    rintro u ⟨neg, i, a, rfl⟩
    exact root_preserves_splitQ_all_ranks K r hr neg i a
  exact hle g.property x

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankQuadraticForm
