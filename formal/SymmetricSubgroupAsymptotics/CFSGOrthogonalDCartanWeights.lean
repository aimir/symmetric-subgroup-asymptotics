import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanMatrices
import Mathlib.Data.Matrix.Cartan

/-! Integer weights of the literal D coroots agree with the precise
untransposed pinned D table, including its two terminal fork nodes. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices

def weight (r : ℕ) (i : Fin r) (x : Index r) : ℤ := cartan ℤ r i x x

theorem weight_inr (r : ℕ) (hr : 4≤r) (i j : Fin r) :
    weight r i (Sum.inr j)=-weight r i (Sum.inl j) := by
  by_cases hi : i.val+1<r <;>
    simp [weight,cartan_eq ℤ r hr,hi,Matrix.single,neg_sub] <;> ring

theorem weight_inl_eq (r : ℕ) (hr : 4≤r) (i j : Fin r) :
    weight r i (Sum.inl j)=
      if i.val+1<r then
        (if i.val=j.val then 1 else 0)-(if i.val+1=j.val then 1 else 0)
      else (if i.val-1=j.val then 1 else 0)+(if i.val=j.val then 1 else 0) := by
  by_cases hi : i.val+1<r <;>
    simp [weight,cartan_eq ℤ r hr,hi,Matrix.single,Fin.ext_iff,previous_val]

theorem weight_chain (r : ℕ) (hr : 4≤r) (i j : Fin r) (hj : j.val+1<r) :
    weight r i (Sum.inl j)-weight r i (Sum.inl (⟨j.val+1,hj⟩ : Fin r))=CartanMatrix.D r i j := by
  have hil := i.isLt
  have hjl := j.isLt
  have hs : ¬r≤2 := by omega
  simp only [weight_inl_eq r hr,CartanMatrix.D,Matrix.of_apply,Fin.ext_iff,if_neg hs]
  split_ifs <;> omega

theorem weight_terminal (r : ℕ) (hr : 4≤r) (i j : Fin r) (hj : ¬j.val+1<r) :
    weight r i (Sum.inl (previous r j))+weight r i (Sum.inl j)=CartanMatrix.D r i j := by
  have hil := i.isLt
  have hjl := j.isLt
  have hs : ¬r≤2 := by omega
  simp only [weight_inl_eq r hr,previous_val,CartanMatrix.D,Matrix.of_apply,Fin.ext_iff,if_neg hs]
  split_ifs <;> omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
