import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCartanMatrices
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreEF

/-! Exact integral coroot weights for the original B-transpose table. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

def weight (r : ℕ) (i : Fin r) (x : Index r) : ℤ := cartan ℤ r i x x

theorem weight_middle (r : ℕ) (i : Fin r) : weight r i (middle r)=0 := by
  by_cases hi : i.val+1<r <;> simp [weight,cartan_eq,hi,Matrix.single,pos,neg,middle]

theorem weight_neg (r : ℕ) (i j : Fin r) : weight r i (neg r j)= -weight r i (pos r j) := by
  by_cases hi : i.val+1<r <;> simp [weight,cartan_eq,hi,Matrix.single,pos,neg,neg_sub]

theorem weight_pos_eq (r : ℕ) (i j : Fin r) : weight r i (pos r j)=
    if i.val+1<r then
      (if i.val=j.val then 1 else 0)-(if i.val+1=j.val then 1 else 0)
    else if i.val=j.val then 2 else 0 := by
  by_cases hi : i.val+1<r <;> simp [weight,cartan_eq,hi,Matrix.single,pos,neg,Fin.ext_iff]

theorem weight_chain (r : ℕ) (i j : Fin r) (hj : j.val+1<r) :
    weight r i (pos r j)-weight r i (pos r (⟨j.val+1,hj⟩ : Fin r))=CartanMatrix.C r i j := by
  have hil := i.isLt
  have hjl := j.isLt
  simp only [weight_pos_eq,CartanMatrix.C,Matrix.of_apply,Fin.ext_iff]
  split_ifs <;> omega

theorem weight_chain_mirror (r : ℕ) (i j : Fin r) (hj : j.val+1<r) :
    weight r i (neg r (⟨j.val+1,hj⟩ : Fin r))-weight r i (neg r j)=CartanMatrix.C r i j := by
  rw [weight_neg,weight_neg]
  have h := weight_chain r i j hj
  omega

theorem weight_terminal (r : ℕ) (i j : Fin r) (hj : ¬j.val+1<r) :
    weight r i (pos r j)=CartanMatrix.C r i j := by
  have hil := i.isLt
  have hjl := j.isLt
  simp only [weight_pos_eq,CartanMatrix.C,Matrix.of_apply,Fin.ext_iff]
  split_ifs <;> omega

theorem cartan_eq_diagonal_weight (r : ℕ) (i : Fin r) :
    cartan ℤ r i=Matrix.diagonal (weight r i) := by
  obtain ⟨d,hd⟩ := cartan_isDiagonal ℤ r i
  have hw : weight r i=d := by funext x;simp only [weight,hd,Matrix.diagonal_apply_eq]
  rw [hw]
  exact hd

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
