import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentRoots
import SymmetricSubgroupAsymptotics.CFSGSymplecticCoordinateShortRoots

/-! Every actual positive GL short-root word lies in the same U. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices

theorem flag_neg_lt_neg (n : ℕ) (i j : Fin n) :
    flagEquiv n (Sum.inr i) < flagEquiv n (Sum.inr j) ↔ j < i := by
  change n + (Fin.rev i).val < n + (Fin.rev j).val ↔ j.val < i.val
  rw [Nat.add_lt_add_iff_left]
  exact Fin.rev_lt_rev

theorem coordinateShort_mem_unipotent (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (i j : Fin (r + 1)) (hij : i < j) (a : K) :
    (⟨coordinateShortUnit K r i j (ne_of_lt hij) a,
      coordinateShortUnit_mem K r hr i j (ne_of_lt hij) a⟩ : elementaryRootGroup K (r + 1)) ∈
      unipotent K (r + 1) := by
  have hpos : flagEquiv (r + 1) (Sum.inl i) ≤ flagEquiv (r + 1) (Sum.inl j) := by
    change i.val ≤ j.val
    exact hij.le
  have hneg : flagEquiv (r + 1) (Sum.inr j) ≤ flagEquiv (r + 1) (Sum.inr i) :=
    ((flag_neg_lt_neg (r + 1) j i).mpr hij).le
  refine ⟨?_, ?_⟩
  · change (Matrix.transvection (Sum.inl i) (Sum.inl j) a *
      Matrix.transvection (Sum.inr j) (Sum.inr i) (-a)).BlockTriangular (flagEquiv (r + 1))
    exact (Matrix.blockTriangular_transvection hpos a).mul
      (Matrix.blockTriangular_transvection hneg (-a))
  · intro x
    change (coordinateShortUnit K r i j (ne_of_lt hij) a : Mat K (r + 1)) x x = 1
    have hX : coordinateShortMatrix K r i j x x = 0 := by
      cases x with
      | inl k =>
        by_cases hik : i = k
        · subst k
          simp [coordinateShortMatrix, Matrix.single_apply, ne_of_lt hij, ne_of_gt hij]
        · simp [coordinateShortMatrix, Matrix.single_apply, hik]
      | inr k =>
        by_cases hjk : j = k
        · subst k
          simp [coordinateShortMatrix, Matrix.single_apply, ne_of_lt hij, ne_of_gt hij]
        · simp [coordinateShortMatrix, Matrix.single_apply, hjk]
    rw [coordinateShortUnit_val]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hX,
      Matrix.one_apply_eq, mul_zero, add_zero]

def coordinateShortInU (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (i j : Fin (r + 1)) (hij : i < j) (a : K) : unipotent K (r + 1) :=
  ⟨⟨coordinateShortUnit K r i j (ne_of_lt hij) a,
      coordinateShortUnit_mem K r hr i j (ne_of_lt hij) a⟩,
    coordinateShort_mem_unipotent K r hr i j hij a⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
