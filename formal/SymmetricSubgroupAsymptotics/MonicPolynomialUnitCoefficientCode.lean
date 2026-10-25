import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.OfFn

/-! A positive monic polynomial with nonzero constant coefficient is
determined by its constant UNIT and its interior coefficient word.
Leading coefficients are forced. The statement is uniform in the field
and contains no matrix or conjugacy assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Polynomial
namespace SymmetricSubgroupAsymptotics.MonicPolynomialUnitCoefficientCode
variable {K : Type*} [Field K]

def code (p : K[X]) (hp0 : p.coeff 0 ≠ 0) : Kˣ × List K :=
  (Units.mk0 (p.coeff 0) hp0,
    List.ofFn (fun i : Fin (p.natDegree-1) => p.coeff (i.val+1)))

theorem length_code (p : K[X]) (hp0 : p.coeff 0 ≠ 0) :
    (code p hp0).2.length=p.natDegree-1 := List.length_ofFn

theorem eq_of_code_eq {p q : K[X]} (hp : p.Monic) (hq : q.Monic)
    (hpd : 0 < p.natDegree) (hqd : 0 < q.natDegree)
    (hp0 : p.coeff 0 ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (he : code p hp0=code q hq0) : p=q := by
  have hd : p.natDegree=q.natDegree := by
    have hh := congrArg (fun z : Kˣ × List K => z.2.length) he
    change (code p hp0).2.length=(code q hq0).2.length at hh
    rw [length_code,length_code] at hh
    omega
  have hconst : p.coeff 0=q.coeff 0 :=
    congrArg (fun z : Kˣ × List K => (z.1 : K)) he
  have hf : (fun i : Fin (p.natDegree-1) => p.coeff (i.val+1))=
      (fun i : Fin (p.natDegree-1) => q.coeff (i.val+1)) := by
    apply List.ofFn_injective
    have hh := congrArg (fun z : Kˣ × List K => z.2) he
    simpa only [code,hd] using hh
  apply Polynomial.ext
  intro j
  by_cases hj0 : j=0
  · subst j
    exact hconst
  by_cases hjd : j=p.natDegree
  · subst j
    rw [hp.coeff_natDegree,hd,hq.coeff_natDegree]
  by_cases hj : j<p.natDegree
  · have hi : j-1<p.natDegree-1 := by omega
    have hh := congrFun hf ⟨j-1,hi⟩
    simpa only [show j-1+1=j by omega] using hh
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end SymmetricSubgroupAsymptotics.MonicPolynomialUnitCoefficientCode
