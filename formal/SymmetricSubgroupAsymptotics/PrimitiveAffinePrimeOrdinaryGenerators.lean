import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeDegreeSource
import SymmetricSubgroupAsymptotics.MetacyclicNormalGenerators

/-! Every faithful primitive affine action of prime degree has at most
two ordinary generators. The actual cyclic point stabilizer is used,
so every prime degree at least five satisfies the literal half-degree
bound without any permutation-generator input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeOrdinaryGenerators

variable {G : Type} [Group G] [Finite G] {n : ℕ}
    [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]
    (P : PrimitiveAffineProfile G (Fin n))

include P in
theorem genRank_le_two (hprimitive : MulAction.IsPreprimitive G (Fin n)) (hn : n.Prime) :
    MarkedC4.genRank G≤2 := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using hn.one_lt)
  let x : Fin n := ⟨0,hn.pos⟩
  letI : IsCyclic (P.complement x) := P.complement_isCyclic_of_degree_prime x hn
  exact (P.genRank_le_complement_add_one hprimitive x).trans
    (by have h : MarkedC4.genRank (P.complement x)≤1 := MarkedC4.genRank_le_one_of_isCyclic
        omega)

include P in
theorem exists_half_degree_generators
    (hprimitive : MulAction.IsPreprimitive G (Fin n)) (hn : n.Prime) (hn5 : 5≤n) :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ 2*S.card≤n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  refine ⟨S,hgen,?_⟩
  have hrank := genRank_le_two P hprimitive hn
  omega

theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (A : PrimitiveAffineProfile J (Fin n))
    (hprimitive : MulAction.IsPreprimitive J (Fin n)) (hn : n.Prime) (hn5 : 5≤n) :
    ∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤n :=
  exists_half_degree_generators A hprimitive hn hn5

end SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeOrdinaryGenerators
