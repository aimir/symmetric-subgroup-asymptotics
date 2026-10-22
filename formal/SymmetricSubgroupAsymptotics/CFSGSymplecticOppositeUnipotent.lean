import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentShortRoots

/-! The actual natural symplectic J conjugates every positive defining
root to its opposite. Both subgroups are in the same original elementary
matrix group. No abstract longest-Weyl or generation input is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOppositeUnipotent
open CFSGSymplecticSerreMatrices CFSGSymplecticUnipotent
variable (K : Type) [Field K]

def oppositionUnit (n : ℕ) : (Mat K n)ˣ where
  val := Matrix.J (Fin n) K
  inv := -Matrix.J (Fin n) K
  val_inv := by rw [Matrix.mul_neg, Matrix.J_squared, neg_neg]
  inv_val := by rw [Matrix.neg_mul, Matrix.J_squared, neg_neg]

def opposition (n : ℕ) : elementaryRootGroup K n :=
  ⟨oppositionUnit K n, CFSGSymplecticStabilizerCoordinates.all_formPreserving_elementary
    K n (oppositionUnit K n) (CFSGSymplecticStabilizerCoordinates.preservesPairing_of_form n _ (SymplecticGroup.J_mem (Fin n) K))⟩

theorem opposition_positive_matrix (n : ℕ) (i : Fin n) :
    Matrix.J (Fin n) K * positive K n i = -(negative K n i * Matrix.J (Fin n) K) := by
  unfold negative
  by_cases hi : i.val + 1 < n
  · let j : Fin n := ⟨i.val+1,hi⟩
    have hE : positive K n i = Matrix.fromBlocks
        (Matrix.single i j 1) 0 0 (-Matrix.single j i 1) := by
      ext x y
      cases x <;> cases y <;> simp [positive, hi, Matrix.fromBlocks, Matrix.single_apply, j]
    rw [hE]
    simp [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.transpose_single, Matrix.fromBlocks_neg]
  · have hE : positive K n i = Matrix.fromBlocks
        0 (Matrix.single i i 1) 0 0 := by
      ext x y
      cases x <;> cases y <;> simp [positive, hi, Matrix.fromBlocks, Matrix.single_apply]
    rw [hE]
    simp [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.transpose_single, Matrix.fromBlocks_neg]

theorem opposition_conjugates_positive (n : ℕ) (i : Fin n) (t : K) :
    opposition K n * elementaryRoot K n false i t * (opposition K n)⁻¹ =
      elementaryRoot K n true i (-t) := by
  have hmul : opposition K n * elementaryRoot K n false i t =
      elementaryRoot K n true i (-t) * opposition K n := by
    apply Subtype.ext
    apply Units.ext
    change Matrix.J (Fin n) K * (1+t • positive K n i) =
      (1+(-t) • negative K n i) * Matrix.J (Fin n) K
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
    rw [opposition_positive_matrix K n i]
    simp
  rw [hmul]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem positive_mem_unipotent (n : ℕ) (i : Fin n) (t : K) :
    elementaryRoot K n false i t ∈ unipotent K n := by
  change (1+t • positive K n i).BlockTriangular (flagEquiv n) ∧
    ∀ x, (1+t • positive K n i) x x = 1
  by_cases hi : i.val + 1 < n
  · let j : Fin n := ⟨i.val+1,hi⟩
    have hij : i < j := by change i.val < i.val + 1; omega
    have hne : i≠j := ne_of_lt hij
    have hp : flagEquiv n (Sum.inl i) ≤ flagEquiv n (Sum.inl j) := by
      change i.val ≤ j.val; exact hij.le
    have hn : flagEquiv n (Sum.inr j) ≤ flagEquiv n (Sum.inr i) :=
      ((flag_neg_lt_neg n j i).mpr hij).le
    have hE : (positive K n i).BlockTriangular (flagEquiv n) := by
      rw [positive, dif_pos hi]
      change ((Matrix.single (Sum.inl i) (Sum.inl j) 1 -
        Matrix.single (Sum.inr j) (Sum.inr i) 1) : Mat K n).BlockTriangular (flagEquiv n)
      exact (Matrix.blockTriangular_single hp 1).sub (Matrix.blockTriangular_single hn 1)
    refine ⟨?_, ?_⟩
    · intro x y hyx
      have hxy : x≠y := by intro h; subst y; exact (lt_irrefl _ hyx)
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hxy, hE hyx]
    · intro x
      have hd : positive K n i x x = 0 := by
        rw [positive, dif_pos hi]
        change ((Matrix.single (Sum.inl i) (Sum.inl j) 1 -
          Matrix.single (Sum.inr j) (Sum.inr i) 1) : Mat K n) x x = 0
        cases x with
        | inl k =>
          by_cases hk : i=k
          · subst k; simp [hne.symm]
          · simp [hk]
        | inr k =>
          by_cases hk : j=k
          · subst k; simp [hne]
          · simp [hk]
      simp [Matrix.add_apply, Matrix.smul_apply, hd]
  · have hE : (positive K n i).BlockTriangular (flagEquiv n) := by
      simpa only [positive, dif_neg hi] using
        (Matrix.blockTriangular_single (flag_pos_lt_neg n i i).le (1:K))
    refine ⟨?_, ?_⟩
    · intro x y hyx
      have hxy : x≠y := by intro h; subst y; exact (lt_irrefl _ hyx)
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hxy, hE hyx]
    · intro x
      cases x <;> simp [positive, hi]

theorem two_unipotents_generate (n : ℕ) :
    Subgroup.closure ((unipotent K n : Set (elementaryRootGroup K n)) ∪
      (unipotent K n).map (MulAut.conj (opposition K n)).toMonoidHom) = ⊤ := by
  apply top_unique
  rw [← elementaryRootSet_generate K n]
  apply Subgroup.closure_mono
  rintro x ⟨neg,i,t,rfl⟩
  cases neg with
  | false => exact Or.inl (positive_mem_unipotent K n i t)
  | true =>
    refine Or.inr ⟨elementaryRoot K n false i (-t), positive_mem_unipotent K n i (-t), ?_⟩
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
      neg_neg] using opposition_conjugates_positive K n i (-t)

end SymmetricSubgroupAsymptotics.CFSGSymplecticOppositeUnipotent
