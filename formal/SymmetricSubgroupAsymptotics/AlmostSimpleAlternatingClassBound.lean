import SymmetricSubgroupAsymptotics.AlmostSimpleAlternatingPermutationEmbedding
import SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionBound
import SymmetricSubgroupAsymptotics.AlternatingPartitionCubeBudget
import SymmetricSubgroupAsymptotics.SymmetricConjugacyPartitionBound

/-! Actual subnormal subgroups of a self-centralizing alternating normal
subgroup extension satisfy the natural partition bound outside degree6.
This retains their faithful image; it does not assert class monotonicity
for arbitrary subgroups of the alternating group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlmostSimpleAlternatingClassBound
open AlmostSimpleAlternatingPermutationEmbedding AlmostSimpleIndexTwoSubnormalClasses

private theorem two_le_partitions (m:ℕ)(hm : 2 ≤ m) : 2 ≤ Nat.card (Nat.Partition m) := by
  let p:Nat.Partition m :=
    { parts := Multiset.replicate m 1
      parts_pos := by
        intro i hi
        have he:i=1 := Multiset.eq_of_mem_replicate hi
        omega
      parts_sum := by simp only [Multiset.sum_replicate,smul_eq_mul,mul_one] }
  let q:Nat.Partition m:=Nat.Partition.indiscrete m
  have hp:p.parts.card=m := by simp [p]
  have hq:q.parts.card=1 := by
    change (Nat.Partition.indiscrete m).parts.card=1
    rw [Nat.Partition.indiscrete_parts (by omega)]
    rfl
  have hpq:p≠q := by
    intro he
    have hh:=congrArg (fun p:Nat.Partition m=>p.parts.card) he
    dsimp only at hh
    rw [hp,hq] at hh
    omega
  letI : Nontrivial (Nat.Partition m) := ⟨⟨p,q,hpq⟩⟩
  have hh:1<Nat.card (Nat.Partition m) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

variable {G:Type}[Group G][Finite G](N:Subgroup G)[N.Normal]

theorem class_card_le_partitions (hC:Subgroup.centralizer (N:Set G)=⊥)
    (m:ℕ)(hm : 5 ≤ m)(hne:m≠6)(e:N≃*alternatingGroup (Fin m))
    (H:Subgroup G)(hH:H.IsSubnormal) : Nat.card (ConjClasses H) ≤ Nat.card (Nat.Partition m) := by
  let f:=ambientHom N m hm hne e
  have hf:Function.Injective f:=ambientHom_injective N m hm hne e hC
  let eH:=H.equivMapOfInjective f hf
  have htransport:Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses (H.map f)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map eH.symm.toMonoidHom)
      (ConjClasses.map_surjective eH.symm.surjective)
  letI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup (by simpa using hm)
  letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp (by simp only [Nat.card_fin];omega)
  have hb:=subnormal_class_card_le (alternatingGroup (Fin m)) alternatingGroup.index_eq_two
    (H.map f) (subnormal_image N m hm hne e H hH)
  have hA:Nat.card (ConjClasses (alternatingGroup (Fin m))) ≤ Nat.card (Nat.Partition m) := by
    simpa only [Fintype.card_fin] using
      AlternatingConjugacyPartitionBound.class_card_le_partitions (I:=Fin m) (by simp only [Fintype.card_fin];omega)
  have hS:Nat.card (ConjClasses (Equiv.Perm (Fin m))) ≤ Nat.card (Nat.Partition m) := by
    simpa only [Fintype.card_fin] using SymmetricConjugacyPartitionBound.class_card_le_partitions (I:=Fin m)
  exact htransport.trans (hb.trans (max_le (two_le_partitions m (by omega)) (max_le hA hS)))

theorem class_cube_le (hC:Subgroup.centralizer (N:Set G)=⊥)
    (m:ℕ)(hm : 5 ≤ m)(hne:m≠6)(e:N≃*alternatingGroup (Fin m))
    (n:ℕ)(hmn : m ≤ n)(H:Subgroup G)(hH:H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(n-1) :=
  (Nat.pow_le_pow_left (class_card_le_partitions N hC m hm hne e H hH) 3).trans
    ((AlternatingSubnormalFibonacciBudget.partition_cube_le m hm).trans
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmn 1)))

end SymmetricSubgroupAsymptotics.AlmostSimpleAlternatingClassBound
