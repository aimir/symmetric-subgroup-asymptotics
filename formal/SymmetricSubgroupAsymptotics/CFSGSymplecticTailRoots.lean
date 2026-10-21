import SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerTailUnits

/-! Original C simple roots on the remaining coordinates are exactly
restrictions of the original successor-index simple roots. Those larger
root words fix the first hyperbolic pair. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

@[simp] theorem tailMatrix_add (r : ℕ) (A B : Mat K (r + 1)) :
    tailMatrix r (A + B) = tailMatrix r A + tailMatrix r B := rfl

@[simp] theorem tailMatrix_sub (r : ℕ) (A B : Mat K (r + 1)) :
    tailMatrix r (A - B) = tailMatrix r A - tailMatrix r B := rfl

@[simp] theorem tailMatrix_smul (r : ℕ) (a : K) (A : Mat K (r + 1)) :
    tailMatrix r (a • A) = a • tailMatrix r A := rfl

omit [Field K] in
theorem tailMatrix_transpose (r : ℕ) (A : Mat K (r + 1)) :
    tailMatrix r A.transpose = (tailMatrix r A).transpose := rfl

@[simp] theorem tailMatrix_single (r : ℕ) (i j : Index r) (a : K) :
    tailMatrix r (Matrix.single (tailIndex r i) (tailIndex r j) a) = Matrix.single i j a := by
  ext k l
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp [tailMatrix, tailIndex, Matrix.single]

theorem tailMatrix_positive (r : ℕ) (i : Fin r) :
    tailMatrix r (positive K (r + 1) i.succ) = positive K r i := by
  by_cases hi : i.val + 1 < r
  · have hi' : i.succ.val + 1 < r + 1 := by simp only [Fin.val_succ]; omega
    rw [positive, dif_pos hi', positive, dif_pos hi]
    change tailMatrix r (Matrix.single (tailIndex r (Sum.inl i))
      (tailIndex r (Sum.inl ⟨i.val + 1, hi⟩)) 1 -
      Matrix.single (tailIndex r (Sum.inr ⟨i.val + 1, hi⟩)) (tailIndex r (Sum.inr i)) 1) = _
    rw [tailMatrix_sub, tailMatrix_single, tailMatrix_single]
  · have hi' : ¬i.succ.val + 1 < r + 1 := by simp only [Fin.val_succ]; omega
    rw [positive, dif_neg hi', positive, dif_neg hi]
    exact tailMatrix_single r (Sum.inl i) (Sum.inr i) 1

theorem tailMatrix_rootMatrix (r : ℕ) (neg : Bool) (i : Fin r) :
    tailMatrix r (rootMatrix K (r + 1) neg i.succ) = rootMatrix K r neg i := by
  cases neg
  · exact tailMatrix_positive r i
  · simpa only [rootMatrix, negative, tailMatrix_transpose] using
      congrArg Matrix.transpose (tailMatrix_positive (K := K) r i)

theorem tailMatrix_rootTransvection (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    tailMatrix r (rootTransvection K (r + 1) neg i.succ t : Mat K (r + 1)) =
      (rootTransvection K r neg i t : Mat K r) := by
  simp only [rootTransvection_val, tailMatrix_add, tailMatrix_smul, tailMatrix_one,
    tailMatrix_rootMatrix]

theorem positive_head_zero (r : ℕ) (i : Fin r) (side : Bool) (j : Index (r + 1)) :
    positive K (r + 1) i.succ (if side then Sum.inr 0 else Sum.inl 0) j = 0 ∧
      positive K (r + 1) i.succ j (if side then Sum.inr 0 else Sum.inl 0) = 0 := by
  unfold positive
  split_ifs <;> cases j <;> cases side <;>
    simp [Matrix.single, Fin.ext_iff]

theorem rootMatrix_head_zero (r : ℕ) (neg : Bool) (i : Fin r)
    (side : Bool) (j : Index (r + 1)) :
    rootMatrix K (r + 1) neg i.succ (if side then Sum.inr 0 else Sum.inl 0) j = 0 ∧
      rootMatrix K (r + 1) neg i.succ j (if side then Sum.inr 0 else Sum.inl 0) = 0 := by
  cases neg
  · exact positive_head_zero r i side j
  · exact (positive_head_zero r i side j).symm

theorem rootTransvection_fixesFirstPair (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    FixesFirstPair r (rootTransvection K (r + 1) neg i.succ t : Mat K (r + 1)) := by
  have hfix (side : Bool) :
      (rootTransvection K (r + 1) neg i.succ t : Mat K (r + 1)) *ᵥ
          Pi.single (if side then Sum.inr 0 else Sum.inl 0) 1 =
        Pi.single (if side then Sum.inr 0 else Sum.inl 0) 1 := by
    funext j
    have hz := (rootMatrix_head_zero (K := K) r neg i side j).2
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, rootTransvection_val,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hz, mul_zero, add_zero]
    simp [Pi.single_apply]
  exact ⟨hfix false, hfix true⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
