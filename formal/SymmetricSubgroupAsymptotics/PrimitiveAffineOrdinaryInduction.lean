import SymmetricSubgroupAsymptotics.PrimitiveAffineEvenOrdinaryInduction
import SymmetricSubgroupAsymptotics.PrimitiveAffineOddOrdinaryInduction
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineFourOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PermutationSmallDegreeOrdinaryGenerators
import Mathlib.Algebra.Ring.Parity

/-! The entire primitive affine branch of the sharp ordinary-generator
induction. Its sole induction premise is the literal subgroup theorem at
strictly smaller degrees, with the full S3 exception preserved. The
original group J and its original n-point action are retained throughout.
This does not prove the nonaffine or imprimitive branches of McIver--Neumann. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryInduction
open PermutationOrdinarySmallerActions

/-- Every actual primitive affine subgroup satisfies the sharp bound,
provided the sharp theorem has been proved at strictly smaller degrees. -/
theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (P : PrimitiveAffineProfile J (Fin n)) (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hthree : n=3→J≠⊤)
    (hbelow : ∀(k : ℕ),k<n→∀K:Subgroup (Equiv.Perm (Fin k)),
      (k=3→K≠⊤)→∃S:Finset K,Subgroup.closure (S:Set K)=⊤ ∧ 2*S.card≤k) :
    ∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤n := by
  by_cases hnsmall:n≤3
  · exact PermutationSmallDegreeOrdinaryGenerators.exists_half_degree_generators n J hnsmall hthree
  have hn4 : 4≤n := by omega
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  by_cases hfour:n=4
  · subst n
    exact PrimitiveAffineFourOrdinaryGenerators.exists_half_degree_generators P hprimitive
  have hn5 : 5≤n := by omega
  by_cases hprime:n.Prime
  · exact PrimitiveAffinePrimeOrdinaryGenerators.exists_half_degree_generators P hprimitive hprime hn5
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v:C.V=>C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  let x : Fin n := ⟨0,by omega⟩
  have hdegree : n=P.p^C.d := by
    simpa only [Nat.card_fin,PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv x
  have hdpos := C.d_pos
  have hd2 : 2≤C.d := by
    by_contra h
    have hd1 : C.d=1 := by omega
    apply hprime
    rw [hdegree,hd1,pow_one]
    exact P.p_prime
  have hb : SmallerActionBound (Nat.card (Fin n)) := by
    simpa only [Nat.card_fin] using smallerActionBound_of_subgroup_generators n hbelow
  by_cases hp:P.p=2
  · have hd3 : 3≤C.d := by
      by_contra h
      have hd : C.d=2 := by omega
      apply hfour
      rw [hdegree,hp,hd]
      norm_num
    have hn8 : 8≤n := by
      rw [hdegree,hp]
      simpa using Nat.pow_le_pow_right (by decide : 0<2) hd3
    have heven : Even (Nat.card (Fin n)) := by
      rw [Nat.card_fin,hdegree,hp]
      exact even_two.pow_of_ne_zero (by omega : C.d≠0)
    simpa only [Nat.card_fin] using
      PrimitiveAffineEvenOrdinaryInduction.exists_half_degree_generators
        P hprimitive heven (by simpa only [Nat.card_fin] using hn8) hb
  · have hp3 : 3≤P.p := by have hh := P.p_prime.two_le; omega
    have hn9 : 9≤n := by
      rw [hdegree]
      have hbase : 9≤P.p^2 := by simpa using Nat.pow_le_pow_left hp3 2
      exact hbase.trans (Nat.pow_le_pow_right P.p_prime.pos hd2)
    simpa only [Nat.card_fin] using
      PrimitiveAffineOddOrdinaryInduction.exists_half_degree_generators
        P hprimitive hp (by simpa only [Nat.card_fin] using hn9) hb

end SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryInduction
