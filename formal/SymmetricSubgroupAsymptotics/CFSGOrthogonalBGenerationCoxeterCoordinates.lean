import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortArrays
import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterMonomial

/-! Original-coordinate permutation geometry of the actual B Coxeter
lift. Reuse here is solely of the proved finite coordinate cycle, not of
any B/C group identification in odd characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationCoxeter
open CFSGOrthogonalBGenerationSignedPermutation CFSGOrthogonalBGenerationShortArrays

private theorem swap_inl {I J : Type*} [DecidableEq I] [DecidableEq J] (a b c : I) :
    Equiv.swap (Sum.inl a : I ⊕ J) (Sum.inl b) (Sum.inl c) =
      Sum.inl (Equiv.swap a b c) := by
  by_cases ha : c = a <;> by_cases hb : c = b <;>
    simp [Equiv.swap_apply_def, ha, hb]

theorem cycle_spatial (r : ℕ) (b : Fin (r + 1) ⊕ Fin (r + 1)) :
    coxeterCycle r (Sum.inl b) =
      Sum.inl (CFSGSymplecticSerreMatrices.coxeterCycle r b) := by
  let R := Equiv.sumCongr (finRotate (r + 1)) (finRotate (r + 1))
  have hR (z : Fin (r + 1) ⊕ Fin (r + 1)) :
      (prefixRowPermutation r).symm (Sum.inl z) = Sum.inl (R z) := by
    cases z <;> rfl
  change (prefixRowPermutation r).symm
    (Equiv.swap (Sum.inl (Sum.inl (Fin.last r))) (Sum.inl (Sum.inr (Fin.last r)))
      (Sum.inl b)) = _
  rw [swap_inl, hR]
  change Sum.inl (R (Equiv.swap (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) b)) =
    Sum.inl (Equiv.swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr (0 : Fin (r + 1))) (R b))
  rw [R.injective.map_swap]
  simp [R, finRotate_last]

@[simp] theorem cycle_middle (r : ℕ) : coxeterCycle r (middle (r + 1)) = middle (r + 1) := by
  change (prefixRowPermutation r).symm
    (Equiv.swap (pos (r + 1) (Fin.last r))
      (CFSGOrthogonalBSerreMatrices.neg (r + 1) (Fin.last r)) (middle (r + 1))) = _
  rw [Equiv.swap_apply_of_ne_of_ne (by intro h; cases h) (by intro h; cases h)]
  rfl

theorem spatial_cycle_paired (r : ℕ) (b : Fin (r + 1) ⊕ Fin (r + 1)) :
    CFSGSymplecticSerreMatrices.coxeterCycle r (paired (r + 1) b) =
      paired (r + 1) (CFSGSymplecticSerreMatrices.coxeterCycle r b) := by
  let R := Equiv.sumCongr (finRotate (r + 1)) (finRotate (r + 1))
  have hR (z : Fin (r + 1) ⊕ Fin (r + 1)) : R (paired (r + 1) z) = paired (r + 1) (R z) := by
    cases z <;> rfl
  have hi : Function.Injective (paired (r + 1)) := by
    intro x y h
    simpa only [paired_paired] using congrArg (paired (r + 1)) h
  have hs (z : Fin (r + 1) ⊕ Fin (r + 1)) :
      paired (r + 1) (Equiv.swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) z) =
      Equiv.swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) (paired (r + 1) z) := by
    have hh := hi.map_swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) z
    change paired (r + 1) (Equiv.swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) z) =
      Equiv.swap (Sum.inr (0 : Fin (r + 1))) (Sum.inl 0) (paired (r + 1) z) at hh
    rw [Equiv.swap_comm (Sum.inr (0 : Fin (r + 1))) (Sum.inl 0)] at hh
    exact hh
  change Equiv.swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) (R (paired (r + 1) b)) =
    paired (r + 1) (Equiv.swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr 0) (R b))
  rw [hR, hs]

@[simp] theorem cycle_positive_last (r : ℕ) :
    coxeterCycle r (pos (r + 1) (Fin.last r)) = CFSGOrthogonalBSerreMatrices.neg (r + 1) 0 := by
  rw [cycle_spatial, CFSGSymplecticSerreMatrices.coxeterCycle_inl_last]

@[simp] theorem cycle_negative_last (r : ℕ) :
    coxeterCycle r (CFSGOrthogonalBSerreMatrices.neg (r + 1) (Fin.last r)) = pos (r + 1) 0 := by
  rw [cycle_spatial, CFSGSymplecticSerreMatrices.coxeterCycle_inr_last]

theorem cycle_positive_shift (r j : ℕ) (hj : j < r) :
    coxeterCycle r (pos (r + 1) ⟨j, Nat.lt_succ_of_lt hj⟩) =
      pos (r + 1) ⟨j + 1, Nat.succ_lt_succ hj⟩ := by
  rw [cycle_spatial, CFSGSymplecticSerreMatrices.coxeterCycle_inl_of_lt r j hj]

theorem cycle_negative_shift (r j : ℕ) (hj : j < r) :
    coxeterCycle r (CFSGOrthogonalBSerreMatrices.neg (r + 1) ⟨j, Nat.lt_succ_of_lt hj⟩) =
      CFSGOrthogonalBSerreMatrices.neg (r + 1) ⟨j + 1, Nat.succ_lt_succ hj⟩ := by
  rw [cycle_spatial, CFSGSymplecticSerreMatrices.coxeterCycle_inr_of_lt r j hj]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeterCoordinates
