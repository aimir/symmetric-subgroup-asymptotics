import SymmetricSubgroupAsymptotics.CFSGSymplecticPairPermutationAction
import SymmetricSubgroupAsymptotics.CFSGTwoPointPermutation
import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialRootLines
import SymmetricSubgroupAsymptotics.CFSGActualMatrixRootLines

/-! All natural GL short-root lines belong to the original elementary
C group, by actual simultaneous coordinate permutations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGActualMatrixRootLines CFSGMonomialUnitRootAction

def coordinateShortMatrix (K : Type) [Field K] (r : ℕ) (i j : Fin (r + 1)) : Mat K (r + 1) :=
  Matrix.single (Sum.inl i) (Sum.inl j) 1 - Matrix.single (Sum.inr j) (Sum.inr i) 1

theorem coordinate_short_root_line (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    HasRootLine (elementaryRootGroup K (r + 1)) (coordinateShortMatrix K r i j) := by
  let k : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩
  have hk : k ≠ 0 := by intro h; have hv := congrArg Fin.val h; change 1 = 0 at hv; omega
  obtain ⟨σ, hσi, hσj⟩ := CFSGTwoPointPermutation.exists_map_two k 0 i j hk hij
  have hX : HasRootLine (elementaryRootGroup K (r + 1)) (initialShortMatrix K r hr) := by
    intro a
    exact ⟨(initialShortRoot K r a).val, (initialShortRoot K r a).property,
      initialShortRoot_coe K r hr a⟩
  have hconj : (pairPermutationUnit K r σ : Mat K (r + 1)) * initialShortMatrix K r hr *
      (↑((pairPermutationUnit K r σ)⁻¹) : Mat K (r + 1)) =
      (1 : K) • coordinateShortMatrix K r i j := by
    unfold initialShortMatrix
    rw [mul_sub, sub_mul, pairPermutationUnit_single_conjugation,
      pairPermutationUnit_single_conjugation]
    change Matrix.single (Sum.inl (σ k)) (Sum.inl (σ 0)) 1 -
      Matrix.single (Sum.inr (σ 0)) (Sum.inr (σ k)) 1 = _
    rw [hσi, hσj, one_smul]
    rfl
  exact hasRootLine_conjugate _ _ (pairPermutationUnit_mem K r σ) _ _ 1 one_ne_zero hconj hX

def coordinateShortUnit (K : Type) [Field K] (r : ℕ) (i j : Fin (r + 1))
    (hij : i ≠ j) (a : K) : (Mat K (r + 1))ˣ :=
  transvectionUnit (Sum.inl i) (Sum.inl j) (by simpa using hij) a *
    transvectionUnit (Sum.inr j) (Sum.inr i) (by simpa using hij.symm) (-a)

theorem coordinateShortUnit_val (K : Type) [Field K] (r : ℕ) (i j : Fin (r + 1))
    (hij : i ≠ j) (a : K) :
    (coordinateShortUnit K r i j hij a : Mat K (r + 1)) =
      1 + a • coordinateShortMatrix K r i j := by
  change Matrix.transvection (Sum.inl i) (Sum.inl j) a *
    Matrix.transvection (Sum.inr j) (Sum.inr i) (-a) = _
  simp only [Matrix.transvection, coordinateShortMatrix, add_mul, mul_add,
    one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ (show (Sum.inl j : Index (r + 1)) ≠ Sum.inr j by intro h; cases h),
    add_zero, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, sub_eq_add_neg]
  simp only [smul_add, smul_neg, neg_one_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hn : (Matrix.single (Sum.inr j) (Sum.inr i) (-a) : Mat K (r + 1)) =
      -Matrix.single (Sum.inr j) (Sum.inr i) a :=
    (Matrix.singleAddMonoidHom (Sum.inr j) (Sum.inr i)).map_neg a
  rw [hn]
  abel

theorem coordinateShortUnit_mem (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (i j : Fin (r + 1)) (hij : i ≠ j) (a : K) :
    coordinateShortUnit K r i j hij a ∈ elementaryRootGroup K (r + 1) := by
  obtain ⟨u, hu, he⟩ := coordinate_short_root_line K r hr i j hij a
  have hue : u = coordinateShortUnit K r i j hij a :=
    Units.ext (he.trans (coordinateShortUnit_val K r i j hij a).symm)
  exact hue ▸ hu

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
