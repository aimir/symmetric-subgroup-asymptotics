import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Finite.Card

/-! Actual symmetric-group conjugacy classes inject into ordinary
partitions, using Mathlib's proved cycle-type conjugacy criterion.
No class-count or partition-cardinality estimate is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SymmetricConjugacyPartitionBound
variable {I : Type*} [Fintype I]

def representative (c : ConjClasses (Equiv.Perm I)) : Equiv.Perm I :=
  Classical.choose (ConjClasses.exists_rep c)

omit [Fintype I] in
theorem mk_representative (c : ConjClasses (Equiv.Perm I)) :
    ConjClasses.mk (representative c)=c := Classical.choose_spec (ConjClasses.exists_rep c)

def classPartition (c : ConjClasses (Equiv.Perm I)) : Nat.Partition (Fintype.card I) :=
  (representative c).partition

theorem classPartition_injective : Function.Injective
    (classPartition : ConjClasses (Equiv.Perm I) → Nat.Partition (Fintype.card I)) := by
  intro c d he
  have hc : IsConj (representative c) (representative d) :=
    Equiv.Perm.partition_eq_of_isConj.mpr he
  have hm := ConjClasses.mk_eq_mk_iff_isConj.mpr hc
  simpa only [mk_representative] using hm

theorem class_card_le_partitions :
    Nat.card (ConjClasses (Equiv.Perm I))≤Nat.card (Nat.Partition (Fintype.card I)) :=
  Nat.card_le_card_of_injective classPartition classPartition_injective

end SymmetricSubgroupAsymptotics.SymmetricConjugacyPartitionBound
