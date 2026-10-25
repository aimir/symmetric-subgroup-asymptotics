import SymmetricSubgroupAsymptotics.FiniteThreeCyclicCompanion
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-! The origin cyclic key is a literal three-cycle matrix. In every
characteristic-two field, a matrix with diagonal u and off-diagonal u+1
commutes with it and has determinant3u+2=u. This supplies every unit as
an actual centralizer determinant, with no field-size search. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SLThreeCharacteristicTwoOriginCentralizer
open scoped Matrix
variable {K : Type*} [Field K] [CharP K 2]

private def originMatrix (u : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  !![(u : K), (u : K)+1, (u : K)+1;
     (u : K)+1, (u : K), (u : K)+1;
     (u : K)+1, (u : K)+1, (u : K)]

private theorem originMatrix_det (u : Kˣ) : (originMatrix u).det=(u : K) := by
  calc
    _ = 3*(u : K)+2 := by simp [originMatrix,Matrix.det_fin_three] <;> ring
    _ = ((2 : K)+1)*(u : K)+2 := by ring
    _ = (u : K) := by rw [CharTwo.two_eq_zero]; simp

private def originUnit (u : Kˣ) : Matrix.GeneralLinearGroup (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (originMatrix u)
    ((originMatrix_det u).trans_ne u.ne_zero)

private theorem originUnit_det (u : Kˣ) : Matrix.GeneralLinearGroup.det (originUnit u)=u := by
  apply Units.ext
  exact originMatrix_det u

private theorem origin_commute (u : Kˣ) :
    FiniteThreeCyclicCompanion.companion (![1,0,0] : Fin 3 → K)*originMatrix u=
      originMatrix u*FiniteThreeCyclicCompanion.companion (![1,0,0] : Fin 3 → K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteThreeCyclicCompanion.companion,originMatrix,Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

theorem determinant_surjective
    (A : Matrix.GeneralLinearGroup (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)=
      FiniteThreeCyclicCompanion.companion (![1,0,0] : Fin 3 → K)) :
    ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup (Fin 3) K,
      Commute A P ∧ Matrix.GeneralLinearGroup.det P=u := by
  intro u
  refine ⟨originUnit u,?_,originUnit_det u⟩
  change A*originUnit u=originUnit u*A
  apply Units.ext
  change (A : Matrix (Fin 3) (Fin 3) K)*originMatrix u=
    originMatrix u*(A : Matrix (Fin 3) (Fin 3) K)
  rw [hA]
  exact origin_commute u

end SymmetricSubgroupAsymptotics.SLThreeCharacteristicTwoOriginCentralizer
