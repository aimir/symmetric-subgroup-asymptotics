import SymmetricSubgroupAsymptotics.PrimitiveSocleSubnormalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingProductClassBound
import SymmetricSubgroupAsymptotics.AlternatingSubnormalFibonacciBudget
import SymmetricSubgroupAsymptotics.SymmetricConjugacyPartitionBound
import SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound
import SymmetricSubgroupAsymptotics.PartitionFibonacciBound

/-! The entire alternating simple type in the large primitive raw
structure satisfies GM for actual SUBNORMAL subgroups. One socle factor
uses actual simple/outer class counts; multiple factors use the checked
order budget. No all-subgroups claim at natural alternating degree is
made, and no bounded small-group census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_card_le_alternating_fib
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (hk : D.factorCount=1)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ≤ 8*Nat.fib (m+1) := by
  letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp (by simp; omega)
  have hsimple : Nat.card (ConjClasses D.Simple) ≤ 2*Nat.fib (m+1) := by
    have he : Nat.card (ConjClasses D.Simple) ≤
        Nat.card (ConjClasses (alternatingGroup (Fin m))) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    have ha := ConjugacyClassSubgroupIndexBound.class_card_le_index_mul
      (alternatingGroup (Fin m))
    rw [alternatingGroup.index_eq_two] at ha
    have hp : Nat.card (ConjClasses (Equiv.Perm (Fin m))) ≤ Nat.card (Nat.Partition m) := by
      simpa only [Fintype.card_fin] using
        (SymmetricConjugacyPartitionBound.class_card_le_partitions (I := Fin m))
    exact he.trans (ha.trans (Nat.mul_le_mul_left 2
      (hp.trans (PartitionFibonacciBound.partition_card_le_fib m))))
  have houter : Nat.card (Outer D.Simple) ≤ 4 := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_le_four m hm
  calc
    Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses D.Simple)*Nat.card (Outer D.Simple) :=
      D.subnormal_class_card_le_of_factor_one hk H hH
    _ ≤ (2*Nat.fib (m+1))*4 := Nat.mul_le_mul hsimple houter
    _ = 8*Nat.fib (m+1) := by ring

theorem NonaffineData.subnormal_class_cube_le_of_alternating_single_index
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (hk : D.factorCount=1)
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X=K.index^D.factorCount) (hn : 1024 ≤ Nat.card X)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hell := CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)
  have hmn : m ≤ Nat.card X := by
    rw [hk,pow_one] at hdegree
    exact (hell.2 K hK).trans_eq hdegree.symm
  exact (Nat.pow_le_pow_left (D.subnormal_class_card_le_alternating_fib m hm e hk H hH) 3).trans
    (AlternatingSubnormalFibonacciBudget.eight_fib_cube_le_of_large_degree
      m (Nat.card X) hn hmn)

theorem NonaffineData.subnormal_class_cube_le_of_alternating
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m)) (hn : 1024 ≤ Nat.card X)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  by_cases hk : 2 ≤ D.factorCount
  · exact D.subgroup_class_cube_le_of_alternating_multiple_factors m hm e hk hn H
  have hk1 : D.factorCount=1 := by have hh := D.factorCount_pos; omega
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subnormal_class_cube_le_of_alternating_single_index m hm e hk1 K hK hdegree hn H hH
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
