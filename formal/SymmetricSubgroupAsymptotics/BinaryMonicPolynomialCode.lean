import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card

/-! A dimension-uniform finite binary code for positive monic polynomials
with nonzero constant coefficient over a field of order two. The leading
and constant coefficients are forced, so only the interior bits are stored. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace SymmetricSubgroupAsymptotics.BinaryMonicPolynomialCode
variable {K : Type*} [Field K] [Fintype K]

theorem zero_or_one (hK : Fintype.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  classical
  have he : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hK])
  have hx : x ∈ ({0, 1} : Finset K) := he.symm ▸ Finset.mem_univ x
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

def bits (p : K[X]) : List Bool := by
  classical
  exact List.ofFn (fun i : Fin (p.natDegree - 1) => decide (p.coeff (i.val + 1) = 1))

theorem length_bits (p : K[X]) : (bits p).length = p.natDegree - 1 :=
  List.length_ofFn

theorem eq_of_bits_eq (hK : Fintype.card K = 2) {p q : K[X]}
    (hp : p.Monic) (hq : q.Monic) (hpd : 0 < p.natDegree) (hqd : 0 < q.natDegree)
    (hp0 : p.coeff 0 ≠ 0) (hq0 : q.coeff 0 ≠ 0) (hbits : bits p = bits q) : p = q := by
  classical
  have hd : p.natDegree = q.natDegree := by
    have hl := congrArg List.length hbits
    rw [length_bits, length_bits] at hl
    omega
  have hf : (fun i : Fin (p.natDegree - 1) => decide (p.coeff (i.val + 1) = 1)) =
      (fun i : Fin (p.natDegree - 1) => decide (q.coeff (i.val + 1) = 1)) := by
    apply List.ofFn_injective
    simpa [bits, hd] using hbits
  apply Polynomial.ext
  intro j
  by_cases hj0 : j = 0
  · subst j
    exact (zero_or_one hK (p.coeff 0)).resolve_left hp0 |>.trans
      ((zero_or_one hK (q.coeff 0)).resolve_left hq0).symm
  by_cases hjd : j = p.natDegree
  · subst j
    rw [hp.coeff_natDegree, hd, hq.coeff_natDegree]
  by_cases hj : j < p.natDegree
  · have hi : j - 1 < p.natDegree - 1 := by omega
    have hb := congrFun hf ⟨j - 1, hi⟩
    have hsub : j - 1 + 1 = j := by omega
    simp only [hsub] at hb
    rcases zero_or_one hK (p.coeff j) with hpj | hpj <;>
      rcases zero_or_one hK (q.coeff j) with hqj | hqj
    · exact hpj.trans hqj.symm
    · simp [hpj, hqj] at hb
    · simp [hpj, hqj] at hb
    · exact hpj.trans hqj.symm
  · rw [coeff_eq_zero_of_natDegree_lt (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

end SymmetricSubgroupAsymptotics.BinaryMonicPolynomialCode
