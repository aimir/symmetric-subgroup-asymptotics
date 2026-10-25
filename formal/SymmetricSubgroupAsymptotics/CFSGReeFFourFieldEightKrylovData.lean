import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightCertificateField
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-! One selected Krylov data packet. The polynomial factorization and
coordinate linear relation are checked here. The root-word action on
these vectors is a separate obligation; no period is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovData
open CFSGReeFFourFieldEightCertificateField Polynomial
open scoped BigOperators

def rawVectors : Fin 26 → Fin 26 → Fin 8 := ![
  ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![5,0,0,0,0,0,0,0,0,1,4,0,0,1,4,4,4,3,3,0,4,4,0,0,0,0],
  ![4,5,7,7,4,7,5,7,7,2,0,1,3,4,7,3,1,6,2,1,3,6,2,5,5,2],
  ![4,0,6,3,5,6,0,6,6,3,3,2,5,7,1,0,6,0,0,1,2,0,1,3,5,3],
  ![6,2,3,3,5,7,5,7,4,0,3,7,0,4,3,2,1,0,0,0,4,1,3,2,4,2],
  ![5,3,7,2,6,7,5,3,0,1,4,0,0,4,0,5,5,2,7,1,1,6,3,0,7,1],
  ![0,3,6,3,1,0,7,0,2,0,2,2,6,7,3,7,0,1,0,0,1,1,6,4,3,5],
  ![2,4,5,2,3,2,7,4,4,7,2,2,4,2,6,0,7,7,3,1,7,1,0,6,6,4],
  ![4,2,2,5,1,2,0,5,3,7,0,2,7,0,1,5,1,7,7,3,6,2,4,1,2,3],
  ![5,6,7,7,2,1,1,1,5,1,1,6,0,0,7,4,1,4,0,7,4,5,5,3,2,0],
  ![3,4,3,2,4,4,6,2,0,1,7,4,2,1,1,2,6,6,4,3,3,3,2,6,3,6],
  ![4,1,6,0,6,6,5,1,1,0,2,3,0,6,3,3,5,3,5,7,2,1,0,5,6,2],
  ![6,0,1,4,6,6,0,6,7,4,4,0,7,4,0,2,5,5,4,4,5,4,6,7,1,2],
  ![4,1,6,6,2,4,6,3,7,7,1,4,4,0,7,3,4,3,0,0,7,4,4,4,7,1],
  ![5,5,0,6,0,5,0,7,4,1,6,7,1,3,6,3,3,4,3,4,2,1,5,1,6,7],
  ![7,3,7,7,3,6,7,3,7,7,0,3,3,6,7,5,0,3,7,0,4,4,2,5,2,0],
  ![4,7,2,5,7,0,4,1,2,3,5,2,0,1,2,7,3,4,0,4,0,2,4,6,1,0],
  ![0,4,3,7,3,0,2,2,0,5,7,7,6,2,3,0,1,1,3,6,6,2,3,0,6,3],
  ![7,4,5,7,4,1,4,2,0,4,5,3,1,0,4,7,1,2,5,6,1,4,3,7,4,0],
  ![4,4,3,7,2,2,2,6,2,6,0,6,2,6,2,3,0,2,6,0,4,7,0,7,2,3],
  ![0,1,3,1,1,5,5,4,5,4,2,0,6,3,0,2,6,7,1,2,6,4,7,5,2,7],
  ![1,7,3,6,5,0,5,6,6,3,2,7,1,7,2,4,4,3,3,4,2,7,7,2,0,1],
  ![0,0,2,7,0,2,6,1,7,1,4,5,1,3,0,6,2,0,3,4,3,0,7,0,4,2],
  ![4,1,4,2,3,1,2,1,2,4,7,1,7,4,5,4,1,4,1,3,7,3,4,1,0,0],
  ![2,5,6,4,5,4,6,1,4,2,0,3,0,1,5,6,0,6,5,7,7,3,4,0,1,3],
  ![6,3,4,2,1,5,1,7,1,6,7,4,6,6,3,3,4,5,2,1,1,2,2,5,0,6]]

def vectors (i : Fin 26) : Fin 26 → Element := fun j => ofBits (rawVectors i j)

def rawPolynomial : Fin 26 → Fin 8 := ![1,7,1,5,5,4,2,5,4,2,4,4,0,0,4,4,2,4,5,2,4,5,5,1,7,1]

def coefficient (i : Fin 26) : Element := ofBits (rawPolynomial i)

def rawQuotient : Fin 85 → Fin 8 := ![1,7,2,7,2,1,1,2,7,5,1,2,5,4,6,6,4,6,3,3,5,0,7,1,4,7,4,3,6,3,1,1,0,3,4,3,6,4,5,2,5,5,5,5,5,2,5,4,6,3,4,3,0,1,1,3,6,3,4,7,4,1,7,0,5,3,3,6,4,6,6,4,5,2,1,5,7,2,1,1,2,7,2,7,1]

noncomputable def annihilator : Element[X] := ∑ i : Fin 26, monomial i.val (coefficient i)

noncomputable def cofactor : Element[X] := ∑ i : Fin 85, monomial i.val (ofBits (rawQuotient i))

def rootWord : List (Bool × (Fin 4 × Fin 8)) := [
  (false,(0,1)),
  (false,(3,1)),
  (false,(1,4)),
  (false,(2,2)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1)),
  (false,(1,3)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1)),
  (false,(0,1)),
  (true,(0,1)),
  (false,(0,1)),
  (false,(3,1)),
  (true,(3,1)),
  (false,(3,1)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1)),
  (false,(0,7)),
  (false,(3,5)),
  (false,(1,1)),
  (false,(2,1)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(2,1)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1)),
  (false,(0,1)),
  (true,(0,1)),
  (false,(0,1)),
  (false,(3,1)),
  (true,(3,1)),
  (false,(3,1)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1)),
  (false,(1,1)),
  (true,(1,1)),
  (false,(1,1)),
  (false,(2,1)),
  (true,(2,1)),
  (false,(2,1))]

def blocks : Fin 2 → Fin 3 → Fin 8 := ![![1,4,3],![7,1,0]]

theorem product_coefficient_certificate : ∀ n : Fin 110,
    ((if n.val = 109 then (1 : Element) else 0) -
      (if n.val = 0 then 1 else 0)) =
      ∑ i : Fin 26, ∑ j : Fin 85,
        if i.val + j.val = n.val then coefficient i * ofBits (rawQuotient j) else 0 := by
  decide +kernel

theorem polynomial_factorization : (X^109-1 : Element[X]) = annihilator*cofactor := by
  apply Polynomial.ext
  intro n
  simp only [annihilator, cofactor, Finset.sum_mul, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_monomial]
  by_cases hn : n < 110
  · rw [Finset.sum_comm]
    exact product_coefficient_certificate ⟨n, hn⟩
  · have hn109 : n ≠ 109 := by omega
    have hn0 : n ≠ 0 := by omega
    have hij : ∀ i : Fin 26, ∀ j : Fin 85, i.val + j.val ≠ n := by
      intro i j
      omega
    simp only [if_neg hn109, if_neg hn0, sub_self, hij,
      if_false, Finset.sum_const_zero]

theorem linear_relation : ∀ j : Fin 26, ∑ i : Fin 26, coefficient i*vectors i j = 0 := by decide +kernel

theorem vector_first : ∀ j : Fin 26, vectors 0 j = (Pi.single 0 (1 : Element) : Fin 26 → Element) j := by decide +kernel

theorem vector_moved : vectors 1 ≠ vectors 0 := by
  intro h
  have he := congrArg (fun v : Fin 26 → Element => v 0) h
  exact (by decide +kernel : vectors 1 0 ≠ vectors 0 0) he

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightKrylovData
