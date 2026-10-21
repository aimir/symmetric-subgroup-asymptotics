import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryCyclePermutation
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationAction

/-! The original D fork Weyl word over an arbitrary field. The second
crossed coordinate rotation has the reverse orientation; keeping it is
essential outside characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkAction
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDBinaryCyclePermutation
open CFSGMatrixPairRotation
variable (K : Type) [Field K]

theorem fork_rotations (s : ℕ) :
    ((simpleWeyl K (s + 2) (last s)).val : Mat K (s + 2)) =
      rotation K (Sum.inl (pen s)) (Sum.inr (last s)) *
        rotation K (Sum.inr (pen s)) (Sum.inl (last s)) := by
  have hp : previous (s + 2) (last s) = pen s := by
    apply Fin.ext
    dsimp [previous, last, pen]
  have hE : positive K (s + 2) (last s) =
      Matrix.single (Sum.inl (pen s)) (Sum.inr (last s)) 1 -
        Matrix.single (Sum.inl (last s)) (Sum.inr (pen s)) 1 := by
    rw [positive, dif_neg (show ¬(last s).val + 1 < s + 2 by dsimp [last]; omega), hp]
  change (1 + (-1 : K) • positive K (s + 2) (last s)) *
      (1 + (1 : K) • negative K (s + 2) (last s)) *
      (1 + (-1 : K) • positive K (s + 2) (last s)) = _
  simp only [negative, hE, Matrix.transpose_sub, Matrix.transpose_single,
    neg_one_smul, one_smul]
  simp [rotation, sub_mul, mul_sub, add_mul, mul_add, pen_ne_last, Ne.symm (pen_ne_last s)] <;>
    abel

private theorem rotation_basis {I : Type*} [Fintype I] [DecidableEq I]
    (p q x : I) (hpq : p ≠ q) :
    rotation K p q *ᵥ Pi.single x 1 =
      (if x = q then (-1 : K) else 1) • Pi.single (Equiv.swap p q x) 1 := by
  by_cases hp : x = p
  · subst x
    rw [rotation_basis_left K p q hpq, Equiv.swap_apply_left, if_neg hpq, one_smul]
  · by_cases hq : x = q
    · subst x
      rw [rotation_basis_right K p q hpq, Equiv.swap_apply_right, if_pos rfl, neg_one_smul]
    · rw [rotation_basis_other K p q x hp hq, Equiv.swap_apply_of_ne_of_ne hp hq,
        if_neg hq, one_smul]

def forkColumnSign (s : ℕ) (a : Index (s + 2)) : K :=
  (if a = Sum.inl (last s) then -1 else 1) *
    (if Equiv.swap (Sum.inr (pen s)) (Sum.inl (last s)) a = Sum.inr (last s)
      then -1 else 1)

theorem forkColumnSign_ne_zero (s : ℕ) (a : Index (s + 2)) :
    forkColumnSign K s a ≠ 0 := by
  unfold forkColumnSign
  split_ifs <;> simp

theorem fork_basis (s : ℕ) (a : Index (s + 2)) :
    ((simpleWeyl K (s + 2) (last s)).val : Mat K (s + 2)) *ᵥ Pi.single a 1 =
      forkColumnSign K s a • Pi.single (forkPerm s a) 1 := by
  have hp : Equiv.swap (Sum.inl (pen s)) (Sum.inr (last s))
      (Equiv.swap (Sum.inr (pen s)) (Sum.inl (last s)) a) = forkPerm s a := by
    change Equiv.swap (Sum.inl (pen s)) (Sum.inr (last s))
      (Equiv.swap (Sum.inr (pen s)) (Sum.inl (last s)) a) =
        Equiv.swap (Sum.inl (pen s)) (Sum.inr (last s))
          (Equiv.swap (Sum.inl (last s)) (Sum.inr (pen s)) a)
    rw [Equiv.swap_comm (Sum.inr (pen s)) (Sum.inl (last s))]
  rw [fork_rotations, ← Matrix.mulVec_mulVec,
    rotation_basis K _ _ _ (by intro h; cases h), Matrix.mulVec_smul,
    rotation_basis K _ _ _ (by intro h; cases h), smul_smul, hp]
  rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkAction
