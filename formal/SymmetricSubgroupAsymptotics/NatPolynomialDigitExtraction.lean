import SymmetricSubgroupAsymptotics.NatNoCarryDigitExtraction
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Indexes

/-! Bounded coefficients of a natural polynomial can be read directly
from its value at B. The bound covers EVERY coefficient, so lower
coefficients cannot carry into the selected digit. -/
set_option autoImplicit false
open scoped BigOperators Polynomial
namespace SymmetricSubgroupAsymptotics.NatPolynomialDigitExtraction

theorem eval_ofFn_eq_ofDigits {n : ℕ} (B : ℕ) (v : Fin n → ℕ) :
    (Polynomial.ofFn n v).eval B=Nat.ofDigits B (List.ofFn v) := by
  rw [Polynomial.ofFn_eq_sum_monomial,Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial,Nat.ofDigits_eq_sum_mapIdx,
    List.mapIdx_eq_ofFn,List.get_ofFn,List.length_ofFn,Fin.val_cast,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

theorem eval_digit_eq_coeff (P : ℕ[X]) (B : ℕ) (hB : 0<B)
    (hcoeff : ∀ k : ℕ, P.coeff k<B) (k : ℕ) :
    (P.eval B / B^k) % B=P.coeff k := by
  let m := P.natDegree+1
  let v : Fin m → ℕ := fun i => P.coeff i.val
  have he : Polynomial.ofFn m v=P :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self P.natDegree)
  have hget : (List.ofFn v).getD k 0=P.coeff k :=
    congrArg (fun Q : ℕ[X] => Q.coeff k) he
  have hvalue : P.eval B=Nat.ofDigits B (List.ofFn v) :=
    (congrArg (fun Q : ℕ[X] => Q.eval B) he).symm.trans
      (eval_ofFn_eq_ofDigits B v)
  rw [hvalue]
  exact (NatNoCarryDigitExtraction.digit_of_ofDigits B hB (List.ofFn v)
    (by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact hcoeff i.val) k).trans hget

end SymmetricSubgroupAsymptotics.NatPolynomialDigitExtraction
