import SymmetricSubgroupAsymptotics.CFSGSymplecticSymmetricRootLines
import SymmetricSubgroupAsymptotics.CFSGMatrixSymmetricDecomposition
import SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits

/-! Every symmetric upper and lower block shear belongs to the SAME
literal elementary C subgroup over every field. The decomposition uses
individual diagonal and paired entries, without inverting two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGActualMatrixRootLines CFSGMatrixShearUnits

private theorem upper_single_val (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (a : K) :
    (upper (Matrix.single i j a) : Mat K (r + 1)) =
      1 + Matrix.single (Sum.inl i) (Sum.inr j) a := by
  ext x y
  cases x <;> cases y <;>
    simp [upper, Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply]

private theorem lower_single_val (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (a : K) :
    (lower (Matrix.single i j a) : Mat K (r + 1)) =
      1 + Matrix.single (Sum.inr i) (Sum.inl j) a := by
  ext x y
  cases x <;> cases y <;>
    simp [lower, Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply]

private theorem upper_pair_val (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (a : K) :
    (upper (Matrix.single i j a + Matrix.single j i a) : Mat K (r + 1)) =
      1 + a • symmetricRootMatrix K r false i j := by
  rw [upper_add]
  change (upper (Matrix.single i j a) : Mat K (r + 1)) *
    (upper (Matrix.single j i a) : Mat K (r + 1)) = _
  rw [upper_single_val, upper_single_val]
  simp [symmetricRootMatrix, coordinatePoint, add_mul, mul_add,
    smul_add, Matrix.smul_single, smul_eq_mul, add_assoc]

private theorem lower_pair_val (K : Type) [Field K] (r : ℕ)
    (i j : Fin (r + 1)) (a : K) :
    (lower (Matrix.single i j a + Matrix.single j i a) : Mat K (r + 1)) =
      1 + a • symmetricRootMatrix K r true i j := by
  rw [lower_add]
  change (lower (Matrix.single i j a) : Mat K (r + 1)) *
    (lower (Matrix.single j i a) : Mat K (r + 1)) = _
  rw [lower_single_val, lower_single_val]
  simp [symmetricRootMatrix, coordinatePoint, add_mul, mul_add,
    smul_add, Matrix.smul_single, smul_eq_mul, add_assoc]

theorem symmetric_upper_mem (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (S : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hS : S.IsSymm) :
    upper S ∈ elementaryRootGroup K (r + 1) := by
  apply CFSGMatrixSymmetricDecomposition.mem_of_diagonal_and_pairs
    (upperParameters (elementaryRootGroup K (r + 1))) _ _ S hS
  · intro i a
    change upper (Matrix.single i i a) ∈ elementaryRootGroup K (r + 1)
    have he : upper (Matrix.single i i a) = coordinateLongUnit K r false i a := by
      apply Units.ext
      rw [upper_single_val]
      rfl
    rw [he]
    exact coordinateLongUnit_mem K r false i a
  · intro i j hij a
    change upper (Matrix.single i j a + Matrix.single j i a) ∈ elementaryRootGroup K (r + 1)
    obtain ⟨u, hu, he⟩ := symmetric_root_line K r hr false i j hij a
    have hue : u = upper (Matrix.single i j a + Matrix.single j i a) :=
      Units.ext (he.trans (upper_pair_val K r i j a).symm)
    exact hue ▸ hu

theorem symmetric_lower_mem (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (S : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hS : S.IsSymm) :
    lower S ∈ elementaryRootGroup K (r + 1) := by
  apply CFSGMatrixSymmetricDecomposition.mem_of_diagonal_and_pairs
    (lowerParameters (elementaryRootGroup K (r + 1))) _ _ S hS
  · intro i a
    change lower (Matrix.single i i a) ∈ elementaryRootGroup K (r + 1)
    have he : lower (Matrix.single i i a) = coordinateLongUnit K r true i a := by
      apply Units.ext
      rw [lower_single_val]
      rfl
    rw [he]
    exact coordinateLongUnit_mem K r true i a
  · intro i j hij a
    change lower (Matrix.single i j a + Matrix.single j i a) ∈ elementaryRootGroup K (r + 1)
    obtain ⟨u, hu, he⟩ := symmetric_root_line K r hr true i j hij a
    have hue : u = lower (Matrix.single i j a + Matrix.single j i a) :=
      Units.ext (he.trans (lower_pair_val K r i j a).symm)
    exact hue ▸ hu

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
