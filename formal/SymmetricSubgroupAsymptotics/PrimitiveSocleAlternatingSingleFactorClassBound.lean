import SymmetricSubgroupAsymptotics.AlmostSimpleAlternatingClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.PrimitiveSocleMinimumDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingProductAllDegrees

/-! The actual original raw alternating type, outside the exceptional
simple degree six, satisfies the GM cube bound at EVERY ambient degree
for subnormal subgroups. The full socle is used to prove faithfulness of
the actual conjugation embedding, not supplied as a new hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X:Type}[Group G][Finite G][Finite X][MulAction G X]

private theorem oneFactor_centerless (D:NonaffineData G X)(hk:D.factorCount=1) :
    IsCenterless (finiteGroupSocle G) := by
  let e:=D.oneFactorEquiv hk
  have hS:=centerless_of_nonabelian_simple D.Simple D.noncommutative
  intro x hx
  apply e.injective
  rw [map_one]
  apply hS
  intro y
  have hh:=congrArg e (hx (e.symm y))
  simpa only [map_mul,MulEquiv.apply_symm_apply] using hh

theorem NonaffineData.subnormal_class_card_le_alternating_single_partitions
    (D:NonaffineData G X)(m:ℕ)(hm : 5 ≤ m)(hne:m≠6)
    (e:D.Simple≃*alternatingGroup (Fin m))(hk:D.factorCount=1)
    (H:Subgroup G)(hH:H.IsSubnormal) : Nat.card (ConjClasses H) ≤ Nat.card (Nat.Partition m) := by
  have hC:=FullSocleSelfCentralizing.centralizer_eq_bot (oneFactor_centerless D hk)
  exact AlmostSimpleAlternatingClassBound.class_card_le_partitions (finiteGroupSocle G) hC
    m hm hne ((D.oneFactorEquiv hk).trans e) H hH

theorem NonaffineData.degree_lower_alternating
    (D:NonaffineData G X)(m:ℕ)(hm : 5 ≤ m)(e:D.Simple≃*alternatingGroup (Fin m)) :
    m ≤ Nat.card X := by
  have hell:=CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)
  exact D.degree_lower_of_proper_index_lower m hell.2

theorem NonaffineData.subnormal_class_cube_le_of_alternating_ne_six_all_degrees
    (D:NonaffineData G X)(m:ℕ)(hm : 5 ≤ m)(hne:m≠6)
    (e:D.Simple≃*alternatingGroup (Fin m))(H:Subgroup G)(hH:H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  by_cases hk : 2 ≤ D.factorCount
  · exact D.subgroup_class_cube_le_of_alternating_multiple_factors_all_degrees m hm e hk H
  have hk1:D.factorCount=1 := by have hp:=D.factorCount_pos;omega
  have hclass:=D.subnormal_class_card_le_alternating_single_partitions m hm hne e hk1 H hH
  exact (Nat.pow_le_pow_left hclass 3).trans
    ((AlternatingSubnormalFibonacciBudget.partition_cube_le m hm).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right (D.degree_lower_alternating m hm e) 1)))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
