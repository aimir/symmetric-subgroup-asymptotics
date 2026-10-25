import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-! A degree-two root argument replaces a sixteen-coefficient search.
Over a four-element field, t*x²+s*x can take only prime-field values
for every x only when s=t². The application supplies an actual nontrivial
determinant in cyclic centralizers outside the cubic scalar blocks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Polynomial
namespace SymmetricSubgroupAsymptotics.QuaternaryLinearizedPolynomialImage

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem exists_value_ne_zero_one (hK : Nat.card K=4) (s t : K) (hne : s≠t^2) :
    ∃ x : K, t*x^2+s*x≠0 ∧ t*x^2+s*x≠1 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K=4 := by simpa only [Nat.card_eq_fintype_card] using hK
  by_contra hex
  have hprime (x : K) : t*x^2+s*x=0 ∨ t*x^2+s*x=1 := by
    by_cases hz : t*x^2+s*x=0
    · exact Or.inl hz
    · exact Or.inr (by
        by_contra ho
        exact hex ⟨x,hz,ho⟩)
  let P : K[X] := Polynomial.monomial 2 (s^2+t)+Polynomial.monomial 1 (t^2+s)
  have hdeg : P.natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_monomial_le _
    · exact (Polynomial.natDegree_monomial_le _).trans (by decide : 1≤2)
  have heval (x : K) : P.eval x=0 := by
    have hx4 : x^4=x := by simpa only [hcard] using FiniteField.pow_card x
    have hsq : (t*x^2+s*x)^2=t^2*x^4+s^2*x^2 := by
      calc
        _ = (t*x^2)^2+(s*x)^2 := by
          rw [add_sq,(show (2 : K)=0 from CharTwo.two_eq_zero)]
          simp only [zero_mul,add_zero]
        _ = _ := by ring
    have he : P.eval x=(t*x^2+s*x)^2+(t*x^2+s*x) := by
      simp only [P,Polynomial.eval_add,Polynomial.eval_monomial,pow_one]
      rw [hsq,hx4]
      ring
    rw [he]
    rcases hprime x with hz | ho
    · rw [hz]; simp
    · rw [ho]; simp only [one_pow,CharTwo.add_self_eq_zero]
  have hlt : 2 < Fintype.card K := by rw [hcard]; decide
  have hzero : P=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    P Function.injective_id heval (hdeg.trans_lt hlt)
  have hc := congrArg (fun Q : K[X] => Q.coeff 1) hzero
  have hcoef : t^2+s=0 := by simpa [P,Polynomial.coeff_monomial] using hc
  exact hne (CharTwo.add_eq_zero.mp hcoef).symm

end SymmetricSubgroupAsymptotics.QuaternaryLinearizedPolynomialImage
