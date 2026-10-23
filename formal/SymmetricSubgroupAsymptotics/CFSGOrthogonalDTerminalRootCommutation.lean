import SymmetricSubgroupAsymptotics.CFSGTwistedDNaturalFork
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements

/-! The two terminal natural D root directions commute in every sign,
already in genuine rank two. This coordinate proof avoids the rank-four
guard on the existing abstract Cartan-relation commutation theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalFork CFSGOrthogonalDBinaryElements
variable (K : Type) [Field K]

theorem positive_pen (s : ℕ) :
    positive K (s + 2) (pen s) =
      Matrix.single (Sum.inl (pen s)) (Sum.inl (last s)) 1 -
        Matrix.single (Sum.inr (last s)) (Sum.inr (pen s)) 1 := by
  have hi : (pen s).val + 1 < s + 2 := by dsimp [pen]; omega
  have hn : (⟨(pen s).val + 1, hi⟩ : Fin (s + 2)) = last s := Fin.ext rfl
  rw [positive, dif_pos hi, hn]

theorem positive_last (s : ℕ) :
    positive K (s + 2) (last s) =
      Matrix.single (Sum.inl (pen s)) (Sum.inr (last s)) 1 -
        Matrix.single (Sum.inl (last s)) (Sum.inr (pen s)) 1 := by
  have hi : ¬(last s).val + 1 < s + 2 := by simp [last]
  rw [positive, dif_neg hi, previous_last]

theorem rootMatrix_commute (s : ℕ) (e f : Bool) :
    Commute (rootMatrix K (s + 2) e (pen s)) (rootMatrix K (s + 2) f (last s)) := by
  change _ * _ = _ * _
  cases e <;> cases f <;>
    simp only [rootMatrix, Bool.false_eq_true, if_false, if_true, negative,
      positive_pen, positive_last, Matrix.transpose_sub, Matrix.transpose_single] <;>
    simp [sub_mul, mul_sub, pen_ne_last, Ne.symm (pen_ne_last s)]

theorem rootTransvection_commute (s : ℕ) (e f : Bool) (a b : K) :
    Commute (rootTransvection K (s + 2) e (pen s) a)
      (rootTransvection K (s + 2) f (last s) b) := by
  have hc := rootMatrix_commute K s e f
  change _ * _ = _ * _
  apply Units.ext
  change (1 + a • rootMatrix K (s + 2) e (pen s)) *
      (1 + b • rootMatrix K (s + 2) f (last s)) =
    (1 + b • rootMatrix K (s + 2) f (last s)) *
      (1 + a • rootMatrix K (s + 2) e (pen s))
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
    mul_smul_comm, hc.eq, smul_add, smul_smul, mul_comm a b]
  abel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation
