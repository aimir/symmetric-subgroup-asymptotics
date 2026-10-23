import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPolarForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation

/-! Literal elementary D matrices preserve their quadratic and polar
forms already in ranks two and three. These statements concern the
same coordinate root matrices, without a low-rank group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllRankQuadraticPreservation
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDGenerationRootArrays CFSGOrthogonalDIndexQuadraticForm
variable (K : Type) [Field K]

theorem nonterminal_root_array (n : ℕ) (neg : Bool) (i : Fin (n + 2))
    (hi : i.val + 1 < n + 2) (a : K) :
    (rootTransvection K (n + 2) neg i a : Mat K (n + 2)) =
      if neg then chainArray (⟨i.val + 1, hi⟩ : Fin (n + 2)) i a
      else chainArray i (⟨i.val + 1, hi⟩ : Fin (n + 2)) a := by
  cases neg <;>
    simp only [rootTransvection, rootMatrix, Bool.false_eq_true, if_false, if_true,
      negative, positive, dif_pos hi, Matrix.transpose_sub, Matrix.transpose_single,
      smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, chainArray] <;> abel

theorem terminal_root_array (n : ℕ) (neg : Bool) (a : K) :
    (rootTransvection K (n + 2) neg (last n) a : Mat K (n + 2)) =
      if neg then minusArray (pen n) (last n) a else plusArray (pen n) (last n) a := by
  cases neg <;>
    simp only [rootTransvection, rootMatrix, Bool.false_eq_true, if_false, if_true,
      negative, CFSGOrthogonalDTerminalRootCommutation.positive_last,
      Matrix.transpose_sub, Matrix.transpose_single, smul_sub, Matrix.smul_single,
      smul_eq_mul, mul_one, minusArray, plusArray, Matrix.transpose_add,
      Matrix.transpose_one] <;> abel

theorem root_preserves (n : ℕ) (neg : Bool) (i : Fin (n + 2)) (a : K)
    (v : Index (n + 2) → K) :
    splitQ K ((rootTransvection K (n + 2) neg i a : Mat K (n + 2)) *ᵥ v) = splitQ K v := by
  by_cases hi : i.val + 1 < n + 2
  · have hij : i ≠ (⟨i.val + 1, hi⟩ : Fin (n + 2)) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = i.val + 1 at hv
      omega
    rw [nonterminal_root_array K n neg i hi a]
    cases neg
    · exact chain_preserves_splitQ K i _ hij a v
    · exact chain_preserves_splitQ K _ i (Ne.symm hij) a v
  · have he : i = last n := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = n + 1
      omega
    subst i
    rw [terminal_root_array K n neg a]
    cases neg
    · exact plus_preserves_splitQ K (pen n) (last n) a v
    · exact minus_preserves_splitQ K (pen n) (last n) a v

theorem elementary_le_quadratic (n : ℕ) :
    elementaryRootGroup K (n + 2) ≤ quadraticPreserving K (n + 2) := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg, i, a, rfl⟩
  exact root_preserves K n neg i a

theorem elementary_preserves (n : ℕ) (u : elementaryRootGroup K (n + 2))
    (v : Index (n + 2) → K) :
    splitQ K ((u.val : Mat K (n + 2)) *ᵥ v) = splitQ K v :=
  elementary_le_quadratic K n u.property v

theorem elementary_preserves_polar (n : ℕ) (u : elementaryRootGroup K (n + 2))
    (v w : Index (n + 2) → K) :
    CFSGOrthogonalDIndexPolarForm.polar K ((u.val : Mat K (n + 2)) *ᵥ v)
      ((u.val : Mat K (n + 2)) *ᵥ w) = CFSGOrthogonalDIndexPolarForm.polar K v w := by
  have h := elementary_preserves K n u (v + w)
  rw [Matrix.mulVec_add, CFSGOrthogonalDIndexPolarForm.splitQ_add,
    CFSGOrthogonalDIndexPolarForm.splitQ_add,
    elementary_preserves K n u v, elementary_preserves K n u w] at h
  exact add_left_cancel h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllRankQuadraticPreservation
