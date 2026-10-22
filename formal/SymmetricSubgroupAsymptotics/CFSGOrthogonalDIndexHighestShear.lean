import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationRootArrays
import SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits
import Mathlib.Tactic.LinearCombination

/-! Actual positive-chain commutators reduce an alternating central
upper block to the highest D root, e0 wedge e1. The argument uses only
its original matrix entries and works unchanged in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexHighestShear
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationRootArrays CFSGMatrixShearUnits
variable (K : Type) [Field K]

theorem highest_shape_of_chain_commutation (s : ℕ) (S : Matrix (Fin (s + 4)) (Fin (s + 4)) K)
    (hdiag : ∀ i, S i i = 0) (hskew : ∀ i j, S i j + S j i = 0)
    (hcomm : ∀ i j : Fin (s + 4), i.val < j.val →
      (upper S : Mat K (s + 4)) * chainArray i j 1 =
        chainArray i j 1 * (upper S : Mat K (s + 4))) :
    S = Matrix.single (0 : Fin (s + 4)) (⟨1, by omega⟩ : Fin (s + 4))
        (S 0 ⟨1, by omega⟩) -
      Matrix.single (⟨1, by omega⟩ : Fin (s + 4)) (0 : Fin (s + 4))
        (S 0 ⟨1, by omega⟩) := by
  let e : Fin (s + 4) := ⟨1, by omega⟩
  have h0e : (0 : Fin (s + 4)) ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have aux (i j k : Fin (s + 4)) (hij : i.val < j.val) (hki : k ≠ i) : S k j = 0 := by
    have he := congrArg (fun A : Mat K (s + 4) => A (Sum.inl k) (Sum.inr i)) (hcomm i j hij)
    dsimp only at he
    have hs : S k i - S k j = S k i := by
      simpa [upper, chainArray, Matrix.mul_apply, Matrix.single_apply, Matrix.fromBlocks,
        Matrix.one_apply, Fintype.sum_sum_type, mul_sub, Finset.sum_sub_distrib,
        hki, Ne.symm hki, eq_comm] using he
    linear_combination -hs
  have hcol (j : Fin (s + 4)) (hj : 2 ≤ j.val) (k : Fin (s + 4)) : S k j = 0 := by
    by_cases hk : k = 0
    · subst k
      exact aux e j 0 (by change 1 < j.val; omega) h0e
    · exact aux 0 j k (by change 0 < j.val; omega) hk
  have hrow (i : Fin (s + 4)) (hi : 2 ≤ i.val) (j : Fin (s + 4)) : S i j = 0 := by
    have h := hskew i j
    rw [hcol i hi j, add_zero] at h
    exact h
  have he0 : S e 0 = -(S 0 e) := by
    have h := hskew e 0
    linear_combination h
  change S = Matrix.single (0 : Fin (s + 4)) e (S 0 e) - Matrix.single e 0 (S 0 e)
  ext i j
  by_cases hi : 2 ≤ i.val
  · have hi0 : i ≠ 0 := by intro he; have hv := congrArg Fin.val he; change i.val = 0 at hv; omega
    have hie : i ≠ e := by intro he; have hv := congrArg Fin.val he; change i.val = 1 at hv; omega
    simp [hrow i hi j, Matrix.single_apply, Ne.symm hi0, Ne.symm hie]
  · by_cases hj : 2 ≤ j.val
    · have hj0 : j ≠ 0 := by intro he; have hv := congrArg Fin.val he; change j.val = 0 at hv; omega
      have hje : j ≠ e := by intro he; have hv := congrArg Fin.val he; change j.val = 1 at hv; omega
      simp [hcol j hj i, Matrix.single_apply, Ne.symm hje, Ne.symm hj0]
    · have hi' : i = 0 ∨ i = e := by
        have hv : i.val = 0 ∨ i.val = 1 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      have hj' : j = 0 ∨ j = e := by
        have hv : j.val = 0 ∨ j.val = 1 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
        simp [Matrix.single_apply, hdiag, h0e, Ne.symm h0e, he0]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexHighestShear
