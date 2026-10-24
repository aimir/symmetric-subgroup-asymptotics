import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorNumerics

/-! The literal half-degree ordinary-generator bound for primitive affine
profiles in uniform parameter tails: binary dimension at least seven,
ternary dimension at least four, p≥5 and dimension at least three, or
p≥7 and dimension at least two. The complement and original point degree
are those of the given action, not supplied as a counting certificate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineUniformOrdinaryGenerators
open PrimitiveAffineOrdinaryGeneratorNumerics

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

theorem two_mul_genRank_le_degree
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (htail : UniformTail P.p C.d) : 2*MarkedC4.genRank G≤Nat.card X := by
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v:C.V=>C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hdegree : Nat.card X=P.p^C.d := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv x
  have hrank := P.genRank_le_binary_dimension_sq_add_one hprimitive C x
    (exponentBudget P.p) (power_exponentBudget P.p P.p_prime.pos)
  exact (Nat.mul_le_mul_left 2 hrank).trans
    ((half_degree_budget P.p C.d htail).trans_eq hdegree.symm)

theorem exists_half_degree_generators
    (hprimitive : MulAction.IsPreprimitive G X) (C : P.ElementaryChart hprimitive)
    (htail : UniformTail P.p C.d) :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤Nat.card X := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  rw [hS]
  exact two_mul_genRank_le_degree P hprimitive C htail

theorem subgroup_half_degree_generators (n : ℕ) [Nontrivial (Fin n)]
    (J : Subgroup (Equiv.Perm (Fin n))) (A : PrimitiveAffineProfile J (Fin n))
    (hprimitive : MulAction.IsPreprimitive J (Fin n)) (C : A.ElementaryChart hprimitive)
    (htail : UniformTail A.p C.d) :
    ∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤n := by
  simpa only [Nat.card_fin] using exists_half_degree_generators A hprimitive C htail

end SymmetricSubgroupAsymptotics.PrimitiveAffineUniformOrdinaryGenerators
