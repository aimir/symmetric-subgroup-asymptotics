import SymmetricSubgroupAsymptotics.FiniteThreeNoncyclicConjugacy
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.Ring

/-! Literal diagonal determinant witnesses centralize the two actual
three-dimensional noncyclic normal forms, over EVERY field. These are
symbolic matrix identities, not a matrix or class enumeration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SLThreeNoncyclicDeterminantCentralizers
open scoped Matrix
variable {K : Type*} [Field K]

private def tailMatrix (u : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![1,1,(u : K)]

private theorem tailMatrix_det (u : Kˣ) : (tailMatrix u).det=(u : K) := by
  simp [tailMatrix,Matrix.det_diagonal,Fin.prod_univ_three]

private def tailUnit (u : Kˣ) : Matrix.GeneralLinearGroup (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (tailMatrix u)
    ((tailMatrix_det u).trans_ne u.ne_zero)

private theorem tailUnit_det (u : Kˣ) : Matrix.GeneralLinearGroup.det (tailUnit u)=u := by
  apply Units.ext
  exact tailMatrix_det u

private theorem diagonal_commute (a b : K) (u : Kˣ) :
    FiniteThreeNoncyclicConjugacy.diagonal a b*tailMatrix u=
      tailMatrix u*FiniteThreeNoncyclicConjugacy.diagonal a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteThreeNoncyclicConjugacy.diagonal,tailMatrix,Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

private theorem jordan_commute (a : K) (u : Kˣ) :
    FiniteThreeNoncyclicConjugacy.jordan a*tailMatrix u=
      tailMatrix u*FiniteThreeNoncyclicConjugacy.jordan a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteThreeNoncyclicConjugacy.jordan,tailMatrix,Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

theorem diagonal_determinant_surjective
    (A : Matrix.GeneralLinearGroup (Fin 3) K) (a b : K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)=FiniteThreeNoncyclicConjugacy.diagonal a b) :
    ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup (Fin 3) K,
      Commute A P ∧ Matrix.GeneralLinearGroup.det P=u := by
  intro u
  refine ⟨tailUnit u,?_,tailUnit_det u⟩
  change A*tailUnit u=tailUnit u*A
  apply Units.ext
  change (A : Matrix (Fin 3) (Fin 3) K)*tailMatrix u=
    tailMatrix u*(A : Matrix (Fin 3) (Fin 3) K)
  rw [hA]
  exact diagonal_commute a b u

theorem jordan_determinant_surjective
    (A : Matrix.GeneralLinearGroup (Fin 3) K) (a : K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)=FiniteThreeNoncyclicConjugacy.jordan a) :
    ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup (Fin 3) K,
      Commute A P ∧ Matrix.GeneralLinearGroup.det P=u := by
  intro u
  refine ⟨tailUnit u,?_,tailUnit_det u⟩
  change A*tailUnit u=tailUnit u*A
  apply Units.ext
  change (A : Matrix (Fin 3) (Fin 3) K)*tailMatrix u=
    tailMatrix u*(A : Matrix (Fin 3) (Fin 3) K)
  rw [hA]
  exact jordan_commute a u

end SymmetricSubgroupAsymptotics.SLThreeNoncyclicDeterminantCentralizers
