import SymmetricSubgroupAsymptotics.LinearMapCyclicEvaluation
import SymmetricSubgroupAsymptotics.BinaryMonicPolynomialCode
import Mathlib.Algebra.CharP.Two
import Lean.Elab.Tactic.Omega

/-! Invertibility excludes the root zero; absence of nonzero fixed
vectors excludes the root one. Over the field of two elements these
force every actual primary label to have degree at least two, so the
retained primary exponent mass is at most half the dimension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Polynomial
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryFixedFreePrimaryDegree
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem degree_two_le (hK : Nat.card K = 2) (p : K[X])
    (hp : p.Monic) (hpos : 0 < p.natDegree)
    (hzero : p.eval 0 ≠ 0) (hone : p.eval 1 ≠ 0) : 2 ≤ p.natDegree := by
  classical
  by_contra hn
  have hd : p.natDegree = 1 := by omega
  have he : p = X + Polynomial.C (p.coeff 0) := hp.eq_X_add_C hd
  letI := Fintype.ofFinite K
  have hk : Fintype.card K = 2 := by simpa only [Nat.card_eq_fintype_card] using hK
  have hc : p.coeff 0 = 1 := by
    rcases BinaryMonicPolynomialCode.zero_or_one hk (p.coeff 0) with hz | ho
    · exact False.elim (hzero (by simpa only [←coeff_zero_eq_eval_zero] using hz))
    · exact ho
  apply hone
  rw [he]
  simp only [eval_add,eval_X,eval_C,hc,CharTwo.add_self_eq_zero]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V] [Finite V]

theorem prime_degree_two_le (hK : Nat.card K = 2) {A : Module.End K V}
    (C : LinearMapPositivePrimaryDecomposition.Chart A) (hA : Function.Surjective A)
    (hfixed : ∀ x : V, A x = x → x = 0) (i : C.cyclic.ι) :
    2 ≤ (C.prime i).natDegree := by
  have hs₀ : Function.Surjective (A-(0 : K) • (LinearMap.id : Module.End K V)) := by simpa using hA
  have hinj : Function.Injective (A-(1 : K) • (LinearMap.id : Module.End K V)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    apply hfixed x
    exact sub_eq_zero.mp (by simpa only [LinearMap.sub_apply,LinearMap.smul_apply,
      one_smul,LinearMap.id_apply] using hx)
  have hs₁ : Function.Surjective (A-(1 : K) • (LinearMap.id : Module.End K V)) :=
    Finite.surjective_of_injective hinj
  exact degree_two_le hK (C.prime i) (C.monic i)
    (Polynomial.natDegree_pos_iff_degree_pos.mpr
      (Polynomial.degree_pos_of_irreducible (C.irreducible i)))
    (LinearMapCyclicEvaluation.primary_eval_ne_zero C 0 hs₀ i)
    (LinearMapCyclicEvaluation.primary_eval_ne_zero C 1 hs₁ i)

theorem twice_exponent_sum_le_dimension (hK : Nat.card K = 2) {A : Module.End K V}
    (C : LinearMapPositivePrimaryDecomposition.Chart A) (hA : Function.Surjective A)
    (hfixed : ∀ x : V, A x = x → x = 0) :
    2 * (∑ i : C.cyclic.ι, C.exponent i) ≤ Module.finrank K V :=
  C.mul_exponent_sum_le_dimension 2 (prime_degree_two_le hK C hA hfixed)

end SymmetricSubgroupAsymptotics.BinaryFixedFreePrimaryDegree
