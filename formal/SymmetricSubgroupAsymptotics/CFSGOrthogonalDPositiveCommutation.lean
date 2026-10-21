import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveSupport
import SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveSerreSupport

/-! Nonadjacent literal D simple roots commute, including the two fork
siblings whose individual matrix products need not vanish. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

private theorem chain_lie_terminal_of_zero (hr : 4≤r) (i j : Fin r)
    (hi : i.val+1<r) (hj : ¬j.val+1<r) (hz : CartanMatrix.D r i j=0) :
    ⁅positive R r i,positive R r j⁆=0 := by
  have hil := i.isLt
  have hjl := j.isLt
  have hpred : i.val+2≠j.val := by
    intro he
    simp only [CartanMatrix.D,Matrix.of_apply,Fin.ext_iff] at hz
    split_ifs at hz <;> omega
  by_cases hp : i=previous r j
  · have hn : (⟨i.val+1,hi⟩ : Fin r)=j := by
      apply Fin.ext
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
    rw [hei]
    simp [positive,hj,Ring.lie_def,sub_mul,mul_sub,hnprev,hnprev.symm]
  · have hn0 : (⟨i.val+1,hi⟩ : Fin r)≠previous r j := by
      intro he
      have hv := congrArg Fin.val he
      simp only [previous_val] at hv
      change i.val+1=j.val-1 at hv
      omega
    have hn1 : (⟨i.val+1,hi⟩ : Fin r)≠j := by
      intro he
      apply hp
      apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [previous_val]
      change i.val+1=j.val at hv
      omega
    simp [positive,hi,hj,Ring.lie_def,sub_mul,mul_sub,hn0,hn0.symm,hn1,hn1.symm]

theorem positive_lie_of_cartan_zero (hr : 4≤r) (i j : Fin r) (hz : CartanMatrix.D r i j=0) :
    ⁅positive R r i,positive R r j⁆=0 := by
  by_cases hi : i.val+1<r
  · by_cases hj : j.val+1<r
    · have hf : i.val+1≠j.val := by
        intro he
        have hil := i.isLt
        have hjl := j.isLt
        simp only [CartanMatrix.D,Matrix.of_apply,Fin.ext_iff] at hz
        split_ifs at hz <;> omega
      have hb : j.val+1≠i.val := by
        intro he
        have hil := i.isLt
        have hjl := j.isLt
        simp only [CartanMatrix.D,Matrix.of_apply,Fin.ext_iff] at hz
        split_ifs at hz <;> omega
      have he : positive R r i=CFSGSymplecticSerreMatrices.positive R r i := by
        simp only [positive,CFSGSymplecticSerreMatrices.positive,dif_pos hi]
      have he' : positive R r j=CFSGSymplecticSerreMatrices.positive R r j := by
        simp only [positive,CFSGSymplecticSerreMatrices.positive,dif_pos hj]
      rw [he,he',Ring.lie_def,
        CFSGSymplecticSerreMatrices.positive_mul_of_not_adjacent R r i j hf hb,
        CFSGSymplecticSerreMatrices.positive_mul_of_not_adjacent R r j i hb hf,sub_self]
    · exact chain_lie_terminal_of_zero R r hr i j hi hj hz
  · by_cases hj : j.val+1<r
    · have hsym : CartanMatrix.D r j i=0 := by
        have hh := congrArg (fun A : Matrix (Fin r) (Fin r) ℤ => A i j) (CartanMatrix.D_transpose r)
        change CartanMatrix.D r j i=CartanMatrix.D r i j at hh
        exact hh.trans hz
      calc
        ⁅positive R r i,positive R r j⁆ = -⁅positive R r j,positive R r i⁆ :=
          (lie_skew _ _).symm
        _=0 := by rw [chain_lie_terminal_of_zero R r hr j i hj hi hsym,neg_zero]
    · have he : i=j := Fin.ext (by have hil := i.isLt;have hjl := j.isLt;omega)
      subst j
      exact lie_self _

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
