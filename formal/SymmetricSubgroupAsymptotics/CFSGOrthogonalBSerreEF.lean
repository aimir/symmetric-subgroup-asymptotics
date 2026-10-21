import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreEF

/-! The mixed positive/negative relations for the literal B matrices.
The terminal coefficients 1 and 2 are retained integrally. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_negative_of_ne (i j : Fin r) (hij : i≠j) :
    ⁅positive R r i,negative R r j⁆=0 := by
  by_cases hi : i.val+1<r
  · by_cases hj : j.val+1<r
    · have hnext : (⟨i.val+1,hi⟩ : Fin r)≠⟨j.val+1,hj⟩ := by
        intro he
        apply hij
        apply Fin.ext
        have hv := congrArg Fin.val he
        change i.val+1=j.val+1 at hv
        omega
      simp [pos,neg,middle,positive,negative,hi,hj,Ring.lie_def,sub_mul,mul_sub,hij,hij.symm,hnext,hnext.symm]
    · simp [pos,neg,middle,positive,negative,hi,hj,Ring.lie_def,sub_mul,mul_sub,hij,hij.symm]
  · by_cases hj : j.val+1<r
    · simp [pos,neg,middle,positive,negative,hi,hj,Ring.lie_def,sub_mul,mul_sub,hij,hij.symm]
    · have he : i=j := by
        apply Fin.ext
        have hil := i.isLt
        have hjl := j.isLt
        omega
      exact (hij he).elim

theorem EF (i j : Fin r) :
    ⁅positive R r i,negative R r j⁆=if i=j then cartan R r i else 0 := by
  by_cases hij : i=j
  · subst j
    exact (if_pos rfl).symm
  · rw [if_neg hij]
    exact positive_negative_of_ne R r i j hij

theorem typeB_transpose : (CartanMatrix.B r).transpose=CartanMatrix.C r := by
  rw [←CFSGSymplecticSerreMatrices.typeC_transpose r,Matrix.transpose_transpose]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
