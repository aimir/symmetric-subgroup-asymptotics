import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreEF

/-! Nonadjacent distinct actual B simple roots have zero products.
Distinctness is essential: a terminal short root has nonzero square. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_mul_of_not_adjacent (i j : Fin r) (hij : i≠j)
    (hf : i.val+1≠j.val) (hb : j.val+1≠i.val) : positive R r i*positive R r j=0 := by
  have hn : ∀h : i.val+1<r,(⟨i.val+1,h⟩ : Fin r)≠j := by
    intro h he
    exact hf (congrArg Fin.val he)
  have hnr : ∀h : j.val+1<r,i≠(⟨j.val+1,h⟩ : Fin r) := by
    intro h he
    exact hb (congrArg Fin.val he).symm
  by_cases hi : i.val+1<r
  · by_cases hj : j.val+1<r
    · simp [positive,hi,hj,sub_mul,mul_sub,hn,hnr,pos,neg,middle]
    · simp [positive,hi,hj,sub_mul,mul_sub,hn,hnr,pos,neg,middle]
  · by_cases hj : j.val+1<r
    · simp [positive,hi,hj,sub_mul,mul_sub,hn,hnr,pos,neg,middle]
    · have he : i=j := by apply Fin.ext;have hil := i.isLt;have hjl := j.isLt;omega
      exact (hij he).elim

theorem positive_lie_of_cartan_zero (i j : Fin r) (hz : CartanMatrix.C r i j=0) :
    ⁅positive R r i,positive R r j⁆=0 := by
  have hij : i≠j := by intro he;subst j;simp [CartanMatrix.C] at hz
  have hf : i.val+1≠j.val := by
    intro hs
    simp only [CartanMatrix.C,Matrix.of_apply,if_neg hij,if_pos hs] at hz
    omega
  have hb : j.val+1≠i.val := by
    intro hs
    have hn : i.val+1≠j.val := by omega
    simp only [CartanMatrix.C,Matrix.of_apply,if_neg hij,if_neg hn,if_pos hs] at hz
    split_ifs at hz <;> omega
  simp only [Ring.lie_def,positive_mul_of_not_adjacent R r i j hij hf hb,
    positive_mul_of_not_adjacent R r j i hij.symm hb hf,sub_self]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
