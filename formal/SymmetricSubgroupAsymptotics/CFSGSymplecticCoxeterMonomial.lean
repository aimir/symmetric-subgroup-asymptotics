import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterAction
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The actual Coxeter word as a signed monomial matrix. The point
permutation is a literal cycle through the positive then negative coordinates.
This permits exact parameter transport without identifying a classical group. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def coxeterCycle (r : ℕ) : Equiv.Perm (Index (r + 1)) :=
  (Equiv.sumCongr (finRotate (r + 1)) (finRotate (r + 1))).trans
    (Equiv.swap (Sum.inl (0 : Fin (r + 1))) (Sum.inr (0 : Fin (r + 1))))

theorem coxeterCycle_inl_of_lt (r j : ℕ) (hj : j < r) :
    coxeterCycle r (Sum.inl (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (r + 1))) =
      Sum.inl (⟨j + 1, Nat.succ_lt_succ hj⟩ : Fin (r + 1)) := by
  change Equiv.swap (Sum.inl (0 : Fin (r + 1)) : Index (r + 1))
    (Sum.inr (0 : Fin (r + 1))) (Sum.inl (finRotate (r + 1) ⟨j, _⟩)) = _
  rw [finRotate_of_lt hj]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hh := congrArg Fin.val (Sum.inl.inj h)
    change j + 1 = 0 at hh
    omega
  · intro h; cases h

theorem coxeterCycle_inr_of_lt (r j : ℕ) (hj : j < r) :
    coxeterCycle r (Sum.inr (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (r + 1))) =
      Sum.inr (⟨j + 1, Nat.succ_lt_succ hj⟩ : Fin (r + 1)) := by
  change Equiv.swap (Sum.inl (0 : Fin (r + 1)) : Index (r + 1))
    (Sum.inr (0 : Fin (r + 1))) (Sum.inr (finRotate (r + 1) ⟨j, _⟩)) = _
  rw [finRotate_of_lt hj]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; cases h
  · intro h
    have hh := congrArg Fin.val (Sum.inr.inj h)
    change j + 1 = 0 at hh
    omega

@[simp] theorem coxeterCycle_inl_last (r : ℕ) :
    coxeterCycle r (Sum.inl (Fin.last r)) = Sum.inr 0 := by
  change Equiv.swap (Sum.inl (0 : Fin (r + 1)) : Index (r + 1))
    (Sum.inr (0 : Fin (r + 1))) (Sum.inl (finRotate (r + 1) (Fin.last r))) = _
  rw [finRotate_last, Equiv.swap_apply_left]

@[simp] theorem coxeterCycle_inr_last (r : ℕ) :
    coxeterCycle r (Sum.inr (Fin.last r)) = Sum.inl 0 := by
  change Equiv.swap (Sum.inl (0 : Fin (r + 1)) : Index (r + 1))
    (Sum.inr (0 : Fin (r + 1))) (Sum.inr (finRotate (r + 1) (Fin.last r))) = _
  rw [finRotate_last, Equiv.swap_apply_right]

def coxeterSign (K : Type) [Field K] (r : ℕ) : Index (r + 1) → K
  | Sum.inl i => if i = Fin.last r then (-1) ^ r else 1
  | Sum.inr i => if i = Fin.last r then (-1) ^ (r + 1) else 1

theorem coxeterSign_ne_zero (K : Type) [Field K] (r : ℕ) (i : Index (r + 1)) :
    coxeterSign K r i ≠ 0 := by
  cases i <;> simp only [coxeterSign] <;> split_ifs
  all_goals first | exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) | exact one_ne_zero

theorem coxeterWeyl_basis (K : Type) [Field K] (r : ℕ) (i : Index (r + 1)) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *ᵥ Pi.single i 1 =
      coxeterSign K r i • Pi.single (coxeterCycle r i) 1 := by
  rcases i with i | i
  · by_cases hi : i = Fin.last r
    · subst i
      simp only [coxeterSign, if_true, coxeterCycle_inl_last]
      have h := coxeterWeyl_basis_positive_last K r
      have hp : naturalCoordinateBasis K r false r =
          coordinateBasis K r false (Fin.last r) := naturalCoordinateBasis_val K r false (Fin.last r)
      have hz : naturalCoordinateBasis K r true 0 =
          coordinateBasis K r true (0 : Fin (r + 1)) := naturalCoordinateBasis_val K r true 0
      rw [hp, hz] at h
      exact h
    · have hir : i.val < r := by
        have hb := i.isLt
        have hne : i.val ≠ r := fun h => hi (Fin.ext h)
        omega
      let j : Fin (r + 1) := ⟨i.val + 1, Nat.succ_lt_succ hir⟩
      have hcycle : coxeterCycle r (Sum.inl i) = Sum.inl j :=
        coxeterCycle_inl_of_lt r i.val hir
      simp only [coxeterSign, hi, if_false, one_smul, hcycle]
      have h := coxeterWeyl_basis_shift K r false i.val hir
      rw [naturalCoordinateBasis_val K r false i,
        naturalCoordinateBasis_val K r false j] at h
      exact h
  · by_cases hi : i = Fin.last r
    · subst i
      simp only [coxeterSign, if_true, coxeterCycle_inr_last]
      have h := coxeterWeyl_basis_negative_last K r
      have hp : naturalCoordinateBasis K r true r =
          coordinateBasis K r true (Fin.last r) := naturalCoordinateBasis_val K r true (Fin.last r)
      have hz : naturalCoordinateBasis K r false 0 =
          coordinateBasis K r false (0 : Fin (r + 1)) := naturalCoordinateBasis_val K r false 0
      rw [hp, hz] at h
      exact h
    · have hir : i.val < r := by
        have hb := i.isLt
        have hne : i.val ≠ r := fun h => hi (Fin.ext h)
        omega
      let j : Fin (r + 1) := ⟨i.val + 1, Nat.succ_lt_succ hir⟩
      have hcycle : coxeterCycle r (Sum.inr i) = Sum.inr j :=
        coxeterCycle_inr_of_lt r i.val hir
      simp only [coxeterSign, hi, if_false, one_smul, hcycle]
      have h := coxeterWeyl_basis_shift K r true i.val hir
      rw [naturalCoordinateBasis_val K r true i,
        naturalCoordinateBasis_val K r true j] at h
      exact h

/-- Row weights are read at the inverse point permutation. -/
theorem coxeterWeyl_monomial (K : Type) [Field K] (r : ℕ) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) =
      CFSGTypeAMonomialMatrices.monomial (coxeterCycle r).symm
        (coxeterSign K r ∘ (coxeterCycle r).symm) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [coxeterWeyl_basis]
  ext j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply,
    CFSGTypeAMonomialMatrices.monomial_apply, Function.comp_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : j = coxeterCycle r i
  · subst j
    simp only [Equiv.symm_apply_apply, if_true, mul_one]
  · have hh : (coxeterCycle r).symm j ≠ i := by
      intro he
      apply h
      simpa only [Equiv.apply_symm_apply] using congrArg (coxeterCycle r) he
    simp only [h, hh, if_false, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
