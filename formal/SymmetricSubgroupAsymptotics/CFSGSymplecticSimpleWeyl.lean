import SymmetricSubgroupAsymptotics.CFSGSymplecticRootParameters
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotation

/-! Actual simple Weyl words in the literal elementary C group. A
chain word is the product of the two disjoint coordinate-pair rotations;
the terminal word is the single paired rotation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def simpleWeyl (K : Type) [Field K] (r : ℕ) (i : Fin r) : elementaryRootGroup K r :=
  elementaryRoot K r false i (-1) * elementaryRoot K r true i 1 *
    elementaryRoot K r false i (-1)

theorem simpleWeyl_terminal_val (K : Type) [Field K] (r : ℕ) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) =
      CFSGMatrixPairRotation.rotation K (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) := by
  change (1 + (-1 : K) • rootMatrix K (r + 1) false (Fin.last r)) *
      (1 + (1 : K) • rootMatrix K (r + 1) true (Fin.last r)) *
      (1 + (-1 : K) • rootMatrix K (r + 1) false (Fin.last r)) = _
  have hE : rootMatrix K (r + 1) false (Fin.last r) =
      Matrix.single (Sum.inl (Fin.last r)) (Sum.inr (Fin.last r)) 1 := by
    simp [rootMatrix, positive]
  have hF : rootMatrix K (r + 1) true (Fin.last r) =
      Matrix.single (Sum.inr (Fin.last r)) (Sum.inl (Fin.last r)) 1 := by
    simp [rootMatrix, negative, positive, Matrix.transpose_single]
  rw [hE, hF]
  simp only [neg_one_smul, one_smul, ← sub_eq_add_neg]
  exact CFSGMatrixPairRotation.word_eq_rotation K _ _ (by intro h; cases h)

theorem simpleWeyl_chain_val (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) =
      CFSGMatrixPairRotation.rotation K (Sum.inl i.castSucc) (Sum.inl i.succ) *
        CFSGMatrixPairRotation.rotation K (Sum.inr i.castSucc) (Sum.inr i.succ) := by
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = i.val + 1 at hv
    omega
  change (1 + (-1 : K) • positive K (r + 1) i.castSucc) *
      (1 + (1 : K) • negative K (r + 1) i.castSucc) *
      (1 + (-1 : K) • positive K (r + 1) i.castSucc) = _
  simp only [neg_one_smul, one_smul, ← sub_eq_add_neg]
  have hE : positive K (r + 1) i.castSucc =
      Matrix.single (Sum.inl i.castSucc) (Sum.inl i.succ) 1 -
        Matrix.single (Sum.inr i.succ) (Sum.inr i.castSucc) 1 := by
    have hi : i.castSucc.val + 1 < r + 1 := Nat.succ_lt_succ i.isLt
    have hs : (⟨i.castSucc.val + 1, hi⟩ : Fin (r + 1)) = i.succ := by
      apply Fin.ext
      rfl
    simp only [positive, dif_pos hi, hs]
  simp only [negative, hE, Matrix.transpose_sub, Matrix.transpose_single]
  simp [CFSGMatrixPairRotation.rotation, sub_mul, mul_sub, add_mul, mul_add,
    hne, Ne.symm hne] <;> abel

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
