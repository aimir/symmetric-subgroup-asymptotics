import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Pi

/-! Integer coordinate vectors are encoded injectively as polynomials.
Evaluation is the positive-power weighted linear functional used to
separate a finite collection of ORIGINAL root degrees. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.CFSGIntegerVectorPolynomial
variable {r : ℕ}

def codePolynomial (x : Fin r→ℤ) : Polynomial ℤ :=
  ∑i : Fin r,Polynomial.monomial i.val (x i)

theorem codePolynomial_coeff (x : Fin r→ℤ) (i : Fin r) :
    (codePolynomial x).coeff i.val=x i := by
  rw [codePolynomial,Polynomial.finsetSum_coeff]
  calc
    (∑j : Fin r,(Polynomial.monomial j.val (x j)).coeff i.val)=
        (Polynomial.monomial i.val (x i)).coeff i.val := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        apply Polynomial.coeff_monomial_of_ne
        intro h
        exact hji (Fin.ext h.symm)
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    _=x i := Polynomial.coeff_monomial_same _ _

theorem codePolynomial_injective : Function.Injective (codePolynomial (r:=r)) := by
  intro x y h
  funext i
  exact (codePolynomial_coeff x i).symm.trans
    ((congrArg (fun p : Polynomial ℤ=>p.coeff i.val) h).trans (codePolynomial_coeff y i))

def weightedSum (t : ℤ) : (Fin r→ℤ)→ₗ[ℤ]ℤ where
  toFun x:=∑i : Fin r,t^i.val*x i
  map_add' := by
    intro x y
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_left_comm _ _ _

theorem eval_codePolynomial (x : Fin r→ℤ) (t : ℤ) :
    (codePolynomial x).eval t=weightedSum t x := by
  rw [codePolynomial,Polynomial.eval_finsetSum]
  change (∑i : Fin r,(Polynomial.monomial i.val (x i)).eval t)=∑i : Fin r,t^i.val*x i
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_monomial,mul_comm]

theorem weightedSum_single (t : ℤ) (i : Fin r) :
    weightedSum t (Pi.single i (1:ℤ))=t^i.val := by
  change (∑j : Fin r,t^j.val*(Pi.single i (1:ℤ) : Fin r→ℤ) j)=t^i.val
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same,mul_one]
  · intro j hj hji
    simp [Pi.single_apply,hji,Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem weightedSum_single_pos (t : ℤ) (ht : 0<t) (i : Fin r) :
    0<weightedSum t (Pi.single i (1:ℤ)) := by
  rw [weightedSum_single]
  exact pow_pos ht _

end SymmetricSubgroupAsymptotics.CFSGIntegerVectorPolynomial
