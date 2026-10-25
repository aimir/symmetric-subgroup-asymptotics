import SymmetricSubgroupAsymptotics.QuaternaryLinearizedPolynomialImage
import SymmetricSubgroupAsymptotics.SLThreeCharacteristicTwoOriginCentralizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Commute.Basic

/-! Actual polynomial centralizers of the cyclic SL3 keys over a
four-element field. Outside the three cubic scalar keys, the root-bound
lemma produces a nontrivial determinant from A+xI; powers cover the
prime-order unit group. The origin uses its symbolic explicit witness.
No coefficient, matrix, or action enumeration is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SLThreeQuaternaryCyclicCentralizer
open scoped Matrix
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private def shiftMatrix (s t x : K) : Matrix (Fin 3) (Fin 3) K :=
  FiniteThreeCyclicCompanion.companion ![1,s,t]+Matrix.scalar (Fin 3) x

private theorem shiftMatrix_eq (s t x : K) :
    shiftMatrix s t x=!![x,0,1; 1,x,s; 0,1,t+x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shiftMatrix,FiniteThreeCyclicCompanion.companion,Matrix.scalar,Matrix.diagonal]

private theorem shiftMatrix_det (s t x : K) :
    (shiftMatrix s t x).det=1+x^3+t*x^2+s*x := by
  calc
    _ = 1+x^3+t*x^2-s*x := by
      rw [shiftMatrix_eq]
      simp [Matrix.det_fin_three] <;> ring
    _ = _ := by rw [CharTwo.sub_eq_add]

private theorem shiftMatrix_commute (s t x : K) :
    FiniteThreeCyclicCompanion.companion ![1,s,t]*shiftMatrix s t x=
      shiftMatrix s t x*FiniteThreeCyclicCompanion.companion ![1,s,t] := by
  let A := FiniteThreeCyclicCompanion.companion (![1,s,t] : Fin 3 → K)
  have hs : Commute A (Matrix.scalar (Fin 3) x) :=
    (Matrix.scalar_commute x (fun a => Commute.all _ a) A).symm
  exact ((Commute.refl A).add_right hs).eq

theorem noncubic_determinant_surjective (hK : Nat.card K=4) (s t : K) (hne : s≠t^2)
    (A : Matrix.GeneralLinearGroup (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)=FiniteThreeCyclicCompanion.companion ![1,s,t]) :
    ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup (Fin 3) K,
      Commute A P ∧ Matrix.GeneralLinearGroup.det P=u := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K=4 := by simpa only [Nat.card_eq_fintype_card] using hK
  obtain ⟨x,hx0,hx1⟩ := QuaternaryLinearizedPolynomialImage.exists_value_ne_zero_one hK s t hne
  have hx : x≠0 := by intro he; subst x; simp at hx0
  have hx3 : x^3=1 := by
    simpa only [hcard,Nat.reduceSub] using FiniteField.pow_card_sub_one_eq_one x hx
  have hd : (shiftMatrix s t x).det=t*x^2+s*x := by
    rw [shiftMatrix_det,hx3,CharTwo.add_self_eq_zero,zero_add]
  let P : Matrix.GeneralLinearGroup (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (shiftMatrix s t x) (hd.trans_ne hx0)
  have hcomm : Commute A P := by
    change A*P=P*A
    apply Units.ext
    change (A : Matrix (Fin 3) (Fin 3) K)*shiftMatrix s t x=
      shiftMatrix s t x*(A : Matrix (Fin 3) (Fin 3) K)
    rw [hA]
    exact shiftMatrix_commute s t x
  have hP : Matrix.GeneralLinearGroup.det P≠1 := by
    intro he
    have hh : (shiftMatrix s t x).det=1 := congrArg (fun u : Kˣ => (u : K)) he
    exact hx1 (hd.symm.trans hh)
  have hu : Nat.card Kˣ=3 := by rw [Nat.card_units,hK]
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro u
  have hp : u ∈ Subgroup.zpowers (Matrix.GeneralLinearGroup.det P) :=
    mem_zpowers_of_prime_card hu hP
  obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  refine ⟨P^k,hcomm.zpow_right k,?_⟩
  rw [map_zpow]
  exact hk

theorem origin_or_noncubic_determinant_surjective
    (hK : Nat.card K=4) (s t : K) (h : (s=0 ∧ t=0) ∨ s≠t^2)
    (A : Matrix.GeneralLinearGroup (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)=FiniteThreeCyclicCompanion.companion ![1,s,t]) :
    ∀ u : Kˣ, ∃ P : Matrix.GeneralLinearGroup (Fin 3) K,
      Commute A P ∧ Matrix.GeneralLinearGroup.det P=u := by
  rcases h with ⟨rfl,rfl⟩ | h
  · exact SLThreeCharacteristicTwoOriginCentralizer.determinant_surjective A hA
  · exact noncubic_determinant_surjective hK s t h A hA

end SymmetricSubgroupAsymptotics.SLThreeQuaternaryCyclicCentralizer
