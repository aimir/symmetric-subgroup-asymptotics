import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationAction
import Mathlib.Algebra.CharP.Two

/-! The binary D fork Weyl word exchanges two crossed coordinate pairs.
These are actions of the original fork root word, with no replacement
by a named orthogonal group or an abstract Weyl group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDSerreMatrices CFSGMatrixPairRotation
variable (K : Type) [Field K] [CharP K 2]

theorem fork_rotations (s : ℕ) :
    ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2)) =
      rotation K (Sum.inl (Fin.last s).castSucc) (Sum.inr (Fin.last (s + 1))) *
        rotation K (Sum.inl (Fin.last (s + 1))) (Sum.inr (Fin.last s).castSucc) := by
  let p : Fin (s + 2) := (Fin.last s).castSucc
  let q : Fin (s + 2) := Fin.last (s + 1)
  have hpq : p ≠ q := by
    intro h
    have hh := congrArg Fin.val h
    change s = s + 1 at hh
    omega
  have hE : positive K (s + 2) q =
      Matrix.single (Sum.inl p) (Sum.inr q) 1 -
        Matrix.single (Sum.inl q) (Sum.inr p) 1 := by
    have hprev : previous (s + 2) q = p := by
      apply Fin.ext
      dsimp [previous, p, q]
    rw [positive, dif_neg (show ¬q.val + 1 < s + 2 by dsimp [q]; omega), hprev]
  change (1 + (-1 : K) • positive K (s + 2) q) *
      (1 + (1 : K) • negative K (s + 2) q) *
      (1 + (-1 : K) • positive K (s + 2) q) =
    rotation K (Sum.inl p) (Sum.inr q) * rotation K (Sum.inl q) (Sum.inr p)
  simp only [negative, hE, Matrix.transpose_sub, Matrix.transpose_single,
    neg_one_smul, one_smul]
  simp [rotation, sub_mul, mul_sub, add_mul, mul_add, hpq, Ne.symm hpq] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.one_apply, sub_eq_add_neg, CharTwo.neg_eq];
      abel)

theorem fork_positive_penultimate (s : ℕ) :
    ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2)) *ᵥ
        Pi.single (Sum.inl (Fin.last s).castSucc) 1 =
      Pi.single (Sum.inr (Fin.last (s + 1))) 1 := by
  rw [fork_rotations, ← Matrix.mulVec_mulVec]
  rw [rotation_basis_other K _ _ _ (by simp) (by intro h; cases h)]
  exact rotation_basis_left K _ _ (by intro h; cases h)

theorem fork_positive_last (s : ℕ) :
    ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2)) *ᵥ
        Pi.single (Sum.inl (Fin.last (s + 1))) 1 =
      Pi.single (Sum.inr (Fin.last s).castSucc) 1 := by
  rw [fork_rotations, ← Matrix.mulVec_mulVec]
  rw [rotation_basis_left K _ _ (by intro h; cases h)]
  exact rotation_basis_other K _ _ _ (by intro h; cases h) (by simp)

theorem fork_negative_penultimate (s : ℕ) :
    ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2)) *ᵥ
        Pi.single (Sum.inr (Fin.last s).castSucc) 1 =
      Pi.single (Sum.inl (Fin.last (s + 1))) 1 := by
  rw [fork_rotations, ← Matrix.mulVec_mulVec]
  rw [rotation_basis_right K _ _ (by intro h; cases h)]
  rw [Matrix.mulVec_neg, rotation_basis_other K _ _ _
    (by intro h; have hh := congrArg Fin.val (Sum.inl.inj h)
        simp only [Fin.val_last, Fin.val_castSucc] at hh; omega)
    (by intro h; cases h)]
  funext x
  exact CharTwo.neg_eq _

theorem fork_negative_last (s : ℕ) :
    ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2)) *ᵥ
        Pi.single (Sum.inr (Fin.last (s + 1))) 1 =
      Pi.single (Sum.inl (Fin.last s).castSucc) 1 := by
  rw [fork_rotations, ← Matrix.mulVec_mulVec]
  rw [rotation_basis_other K _ _ _ (by intro h; cases h)
    (by intro h; have hh := congrArg Fin.val (Sum.inr.inj h)
        simp only [Fin.val_last, Fin.val_castSucc] at hh; omega)]
  rw [rotation_basis_right K _ _ (by intro h; cases h)]
  funext x
  exact CharTwo.neg_eq _

theorem fork_basis_other (s : ℕ) (j : Index (s + 2))
    (hjp : j ≠ Sum.inl (Fin.last s).castSucc)
    (hjq : j ≠ Sum.inl (Fin.last (s + 1)))
    (hjnp : j ≠ Sum.inr (Fin.last s).castSucc)
    (hjnq : j ≠ Sum.inr (Fin.last (s + 1))) :
    ((simpleWeyl K (s + 2) (Fin.last (s + 1))).val : Mat K (s + 2)) *ᵥ
      Pi.single j 1 = Pi.single j 1 := by
  rw [fork_rotations, ← Matrix.mulVec_mulVec,
    rotation_basis_other K _ _ _ hjq hjnp,
    rotation_basis_other K _ _ _ hjp hjnq]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
