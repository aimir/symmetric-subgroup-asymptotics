import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialLongRoots

/-! The two commuting actual root lines used by the nonbinary
extraction. The short root is the first original negative simple root;
the long root is the actual second-coordinate conjugate already built. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def initialShortRoot (K : Type) [Field K] (r : ℕ) (a : K) : elementaryRootGroup K (r + 1) :=
  elementaryRoot K (r + 1) true 0 a

def initialShortMatrix (K : Type) [Field K] (r : ℕ) (hr : 0 < r) : Mat K (r + 1) :=
  Matrix.single (Sum.inl (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) (Sum.inl 0) 1 -
    Matrix.single (Sum.inr (0 : Fin (r + 1))) (Sum.inr (⟨1, Nat.succ_lt_succ hr⟩ : Fin (r + 1))) 1

theorem initialShortRoot_coe (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (a : K) :
    ((initialShortRoot K r a).val : Mat K (r + 1)) = 1 + a • initialShortMatrix K r hr := by
  change 1 + a • rootMatrix K (r + 1) true 0 = _
  simp only [rootMatrix, if_true, negative, positive, Fin.val_zero,
    show 0 + 1 < r + 1 by omega, dite_true, Matrix.transpose_sub, Matrix.transpose_single,
    initialShortMatrix]

@[simp] theorem initialShortRoot_zero (K : Type) [Field K] (r : ℕ) :
    initialShortRoot K r 0 = 1 := elementaryRoot_zero K (r + 1) true 0

theorem initialShortRoot_add (K : Type) [Field K] (r : ℕ) (a b : K) :
    initialShortRoot K r (a + b) = initialShortRoot K r a * initialShortRoot K r b :=
  elementaryRoot_add K (r + 1) true 0 a b

@[simp] theorem firstLongRoot_zero (K : Type) [Field K] (r : ℕ) :
    firstLongRoot K r 0 = 1 := by
  simp only [firstLongRoot, neg_zero, elementaryRoot_zero, mul_one, mul_inv_cancel]

theorem firstLongRoot_add (K : Type) [Field K] (r : ℕ) (a b : K) :
    firstLongRoot K r (a + b) = firstLongRoot K r a * firstLongRoot K r b := by
  simp only [firstLongRoot, neg_add, elementaryRoot_add, mul_assoc, inv_mul_cancel_left]

@[simp] theorem secondLongRoot_zero (K : Type) [Field K] (r : ℕ) :
    secondLongRoot K r 0 = 1 := by
  simp only [secondLongRoot, firstLongRoot_zero, mul_one, mul_inv_cancel]

theorem secondLongRoot_add (K : Type) [Field K] (r : ℕ) (a b : K) :
    secondLongRoot K r (a + b) = secondLongRoot K r a * secondLongRoot K r b := by
  simp only [secondLongRoot, firstLongRoot_add, mul_assoc, inv_mul_cancel_left]

theorem initial_root_lines_commute (K : Type) [Field K] (r : ℕ) (hr : 0 < r) (a b : K) :
    Commute (initialShortRoot K r a) (secondLongRoot K r b) := by
  let j : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩
  let L : Mat K (r + 1) := Matrix.single (Sum.inl j) (Sum.inr j) 1
  have hj : (0 : Fin (r + 1)) ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have hXL : initialShortMatrix K r hr * L = 0 := by
    simp [initialShortMatrix, L, j, sub_mul, hj]
  have hLX : L * initialShortMatrix K r hr = 0 := by
    simp [initialShortMatrix, L, j, mul_sub, Ne.symm hj]
  have hlong : ((secondLongRoot K r b).val : Mat K (r + 1)) = 1 + b • L := by
    rw [secondLongRoot_coe K r hr]
    simp only [Matrix.transvection, L, j, Matrix.smul_single, smul_eq_mul, mul_one]
  change initialShortRoot K r a * secondLongRoot K r b =
    secondLongRoot K r b * initialShortRoot K r a
  apply Subtype.ext
  apply Units.ext
  change ((initialShortRoot K r a).val : Mat K (r + 1)) *
      ((secondLongRoot K r b).val : Mat K (r + 1)) =
    ((secondLongRoot K r b).val : Mat K (r + 1)) *
      ((initialShortRoot K r a).val : Mat K (r + 1))
  rw [initialShortRoot_coe K r hr, hlong]
  simp only [Matrix.mul_add, Matrix.add_mul, mul_one, one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, hXL, hLX, smul_zero, add_zero]
  abel

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
