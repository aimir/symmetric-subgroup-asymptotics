import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreEF

/-! The literal D-root matrices satisfy the mixed EF relations. Shared
chain cases reuse the already proved paired-chain matrix identities. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

private theorem chain_positive_eq (i : Fin r) (hi : i.val+1<r) :
    positive R r i=CFSGSymplecticSerreMatrices.positive R r i := by
  simp only [positive,CFSGSymplecticSerreMatrices.positive,dif_pos hi]

private theorem chain_negative_eq (i : Fin r) (hi : i.val+1<r) :
    negative R r i=CFSGSymplecticSerreMatrices.negative R r i := by
  exact congrArg Matrix.transpose (chain_positive_eq R r i hi)

private theorem chain_positive_negative_terminal (hr : 4≤r) (i j : Fin r)
    (hi : i.val+1<r) (hj : ¬j.val+1<r) : ⁅positive R r i,negative R r j⁆=0 := by
  have hij : i≠j := by intro he;subst j;exact hj hi
  have hej : negative R r j=
      Matrix.single (Sum.inr j) (Sum.inl (previous r j)) 1-
        Matrix.single (Sum.inr (previous r j)) (Sum.inl j) 1 := by
    simp only [negative,positive,dif_neg hj,Matrix.transpose_sub,Matrix.transpose_single]
  by_cases hp : i=previous r j
  · have hn : (⟨i.val+1,hi⟩ : Fin r)=j := by
      apply Fin.ext
      have hjl := j.isLt
      have hv := congrArg Fin.val hp
      simp only [previous_val] at hv
      change i.val+1=j.val
      omega
    have hei : positive R r i=
        Matrix.single (Sum.inl (previous r j)) (Sum.inl j) 1-
          Matrix.single (Sum.inr j) (Sum.inr (previous r j)) 1 := by
      simp only [positive,dif_pos hi,hn]
      rw [hp]
    have hnprev := previous_ne_of_last r hr j hj
    rw [hei,hej]
    simp [Ring.lie_def,sub_mul,mul_sub,hnprev,hnprev.symm]
  · rw [hej]
    simp [positive,hi,Ring.lie_def,sub_mul,mul_sub,hij,Ne.symm hij,hp,Ne.symm hp]

theorem mixed_transpose (i j : Fin r) :
    ⁅positive R r i,negative R r j⁆.transpose=⁅positive R r j,negative R r i⁆ := by
  simp only [Ring.lie_def,negative,Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_transpose]

theorem positive_negative_of_ne (hr : 4≤r) (i j : Fin r) (hij : i≠j) :
    ⁅positive R r i,negative R r j⁆=0 := by
  by_cases hi : i.val+1<r
  · by_cases hj : j.val+1<r
    · rw [chain_positive_eq R r i hi,chain_negative_eq R r j hj]
      exact CFSGSymplecticSerreMatrices.positive_negative_of_ne R r i j hij
    · exact chain_positive_negative_terminal R r hr i j hi hj
  · by_cases hj : j.val+1<r
    · have hh := congrArg Matrix.transpose (chain_positive_negative_terminal R r hr j i hj hi)
      simpa only [mixed_transpose,Matrix.transpose_zero] using hh
    · exact (hij (Fin.ext (by have hil := i.isLt;have hjl := j.isLt;omega))).elim

theorem EF (hr : 4≤r) (i j : Fin r) :
    ⁅positive R r i,negative R r j⁆=if i=j then cartan R r i else 0 := by
  by_cases hij : i=j
  · subst j
    exact (if_pos rfl).symm
  · rw [if_neg hij]
    exact positive_negative_of_ne R r hr i j hij

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
