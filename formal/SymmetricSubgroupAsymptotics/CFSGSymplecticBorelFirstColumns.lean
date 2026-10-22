import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentRoots

/-! The first two actual isotropic columns of the same C-Borel.
These are literal upper-flag identities, before any form or order argument. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem borel_first_vector (r : ℕ) (g : borel K (r + 1)) :
    (g.val.val : Mat K (r + 1)) *ᵥ Pi.single (Sum.inl (0 : Fin (r + 1))) 1 =
      ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl 0)) • Pi.single (Sum.inl 0) 1 := by
  rw [Matrix.mulVec_single_one]
  funext x
  cases x with
  | inl i =>
    by_cases hi : i = 0
    · subst i
      simp [Matrix.col_apply, Pi.single_apply]
    · have hflag : flagEquiv (r + 1) (Sum.inl (0 : Fin (r + 1))) <
          flagEquiv (r + 1) (Sum.inl i) := by
        change 0 < i.val
        have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      simpa [Matrix.col_apply, Pi.single_apply, hi, Ne.symm hi] using g.property hflag
  | inr i =>
    simpa [Matrix.col_apply, Pi.single_apply] using g.property (flag_pos_lt_neg (r + 1) 0 i)

theorem borel_second_vector (r : ℕ) (hr : 0 < r) (g : borel K (r + 1)) :
    let k : Fin (r + 1) := ⟨1, by omega⟩
    (g.val.val : Mat K (r + 1)) *ᵥ Pi.single (Sum.inl k) 1 =
      ((g.val.val : Mat K (r + 1)) (Sum.inl k) (Sum.inl k)) • Pi.single (Sum.inl k) 1 +
        ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl k)) • Pi.single (Sum.inl 0) 1 := by
  dsimp only
  let k : Fin (r + 1) := ⟨1, by omega⟩
  rw [Matrix.mulVec_single_one]
  funext x
  change (g.val.val : Mat K (r + 1)) x (Sum.inl k) =
    ((((g.val.val : Mat K (r + 1)) (Sum.inl k) (Sum.inl k)) • Pi.single (Sum.inl k) 1 +
      ((g.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inl k)) • Pi.single (Sum.inl 0) 1) :
        Index (r + 1) → K) x
  cases x with
  | inl i =>
    by_cases hi0 : i = 0
    · subst i
      simp [Pi.single_apply, k]
    · by_cases hik : i = k
      · subst i
        simp [Pi.single_apply, k]
      · have hi : k.val < i.val := by
          have hn0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          have hn1 : i.val ≠ 1 := fun h => hik (Fin.ext h)
          dsimp only [k]
          omega
        have hflag : flagEquiv (r + 1) (Sum.inl k) < flagEquiv (r + 1) (Sum.inl i) := hi
        simpa [Pi.single_apply, hi0, hik, Ne.symm hi0, Ne.symm hik] using g.property hflag
  | inr i =>
    simpa [Pi.single_apply] using g.property (flag_pos_lt_neg (r + 1) k i)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
