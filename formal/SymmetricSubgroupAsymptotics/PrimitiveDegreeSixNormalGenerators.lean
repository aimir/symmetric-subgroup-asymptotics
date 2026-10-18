import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixChiefPublished
import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators

/-! The existing explicitly published primitive degree-six classification
also gives an all-normal one-generator bound for the actual primitive
group. The classification remains an explicit input; no assertion about
an arbitrary subgroup of a classified ambient group is used. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveDegreeSixNormalGenerators

variable (h6 : PublishedPrimitiveDegreeSixClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]

include h6 in
theorem normal_generating_singletons (hdegree : Nat.card X = 6) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 1 → G, Subgroup.normalClosure (Set.range x) = N := by
  rcases h6 G X hdegree with h | h | h | h <;> rcases h with ⟨e⟩
  · exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        (AlternatingSymmetricNormalChain.alternating_normal_total (by norm_num : 5 ≤ Nat.card (Fin 5))))
  · exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        (AlternatingSymmetricNormalChain.symmetric_normal_total (by norm_num : 5 ≤ Nat.card (Fin 5))))
  · exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        (AlternatingSymmetricNormalChain.alternating_normal_total (by norm_num : 5 ≤ Nat.card (Fin 6))))
  · exact normal_generating_tuples_of_surjective e.symm.toMonoidHom e.symm.surjective
      (normal_generating_singletons_of_finite_normal_total
        (AlternatingSymmetricNormalChain.symmetric_normal_total (by norm_num : 5 ≤ Nat.card (Fin 6))))

include h6 in
theorem normalGen_le_one (hdegree : Nat.card X = 6)
    (N : Subgroup G) [N.Normal] : MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := normal_generating_singletons h6 G X hdegree N inferInstance
  exact normalGen_le_of_fin_tuple x hx

end SymmetricSubgroupAsymptotics.PrimitiveDegreeSixNormalGenerators

end
