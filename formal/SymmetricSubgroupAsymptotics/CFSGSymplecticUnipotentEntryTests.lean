import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentShortRoots
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentCenterShear

/-! Actual sparse C-root words test every upper entry of the isotropic
complete flag. The paired extra matrix entry lies in a different row,
so no abstract flag-recognition premise is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem coordinateShort_displacement_pos (r : ℕ) (i j : Fin (r + 1))
    (hij : i ≠ j) (a : K) (v : Index (r + 1) → K) :
    (((coordinateShortUnit K r i j hij a : Mat K (r + 1)) *ᵥ v) - v) (Sum.inl i) =
      a * v (Sum.inl j) := by
  rw [coordinateShortUnit_val, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  simp [coordinateShortMatrix, Matrix.sub_mulVec, Matrix.single_mulVec, Pi.single_apply]

theorem coordinateShort_displacement_neg (r : ℕ) (i j : Fin (r + 1))
    (hij : i ≠ j) (a : K) (v : Index (r + 1) → K) :
    (((coordinateShortUnit K r i j hij a : Mat K (r + 1)) *ᵥ v) - v) (Sum.inr j) =
      -a * v (Sum.inr i) := by
  rw [coordinateShortUnit_val, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  simp [coordinateShortMatrix, Matrix.sub_mulVec, Matrix.single_mulVec, Pi.single_apply]

theorem unipotent_entry_test (r : ℕ) (hr : 0 < r)
    (i j : Index (r + 1)) (hij : flagEquiv (r + 1) i < flagEquiv (r + 1) j) :
    ∃ u : unipotent K (r + 1), ∀ v : Index (r + 1) → K,
      (((u.val.val : Mat K (r + 1)) *ᵥ v) - v) i = v j := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hij' : i < j := hij
      refine ⟨coordinateShortInU K r hr i j hij' 1, ?_⟩
      intro v
      change (((coordinateShortUnit K r i j (ne_of_lt hij') 1 : Mat K (r + 1)) *ᵥ v) - v)
        (Sum.inl i) = v (Sum.inl j)
      simpa only [one_mul] using coordinateShort_displacement_pos r i j (ne_of_lt hij') (1 : K) v
    | inr j =>
      by_cases h : i = j
      · subst j
        refine ⟨diagonalLongInU (K := K) r hr i, ?_⟩
        intro v
        rw [diagonalLongInU_val, Matrix.add_mulVec, Matrix.one_mulVec]
        simp [Matrix.single_mulVec, Pi.single_apply]
      · let S : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
          Matrix.single i j 1 + Matrix.single j i 1
        have hS : S.IsSymm := by
          change S.transpose = S
          simp only [S, Matrix.transpose_add, Matrix.transpose_single, add_comm]
        refine ⟨upperShearInU K r hr S hS, ?_⟩
        intro v
        change (((Matrix.fromBlocks 1 S 0 1 : Mat K (r + 1)) *ᵥ v) - v) (Sum.inl i) = v (Sum.inr j)
        simp [Matrix.fromBlocks_mulVec, S, Matrix.add_mulVec, Matrix.single_mulVec,
          Pi.single_apply, h, Ne.symm h]
  | inr i =>
    cases j with
    | inl j => exact False.elim ((not_lt_of_gt (flag_pos_lt_neg (r + 1) j i)) hij)
    | inr j =>
      have hji : j < i := (flag_neg_lt_neg (r + 1) i j).mp hij
      refine ⟨coordinateShortInU K r hr j i hji (-1), ?_⟩
      intro v
      change (((coordinateShortUnit K r j i (ne_of_lt hji) (-1) : Mat K (r + 1)) *ᵥ v) - v)
        (Sum.inr i) = v (Sum.inr j)
      simpa only [neg_neg, one_mul] using
        coordinateShort_displacement_neg r j i (ne_of_lt hji) (-1 : K) v

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
