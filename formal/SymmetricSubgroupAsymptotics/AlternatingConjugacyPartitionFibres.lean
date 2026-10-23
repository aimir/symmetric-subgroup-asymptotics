import SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeConjugacy
import SymmetricSubgroupAsymptotics.DistinctOddPartitionInjection
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Group

/-! Literal alternating conjugacy partitions and their two-coset cover.
A symmetric centralizer contained in A_n forces a distinct-odd FULL
partition, including the fixed-point parts of length one. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionFibres
open Equiv Equiv.Perm
variable {I:Type*}[Fintype I][DecidableEq I]

abbrev A := alternatingGroup I

def representative (c:ConjClasses (A (I:=I))) : A (I:=I) := Classical.choose (ConjClasses.exists_rep c)

theorem mk_representative (c:ConjClasses (A (I:=I))) : ConjClasses.mk (representative c)=c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

def classPartition (c:ConjClasses (A (I:=I))) : Nat.Partition (Fintype.card I) :=
  (representative c).val.partition

theorem classPartition_mk (p:A (I:=I)) : classPartition (ConjClasses.mk p)=p.val.partition := by
  have hc:IsConj (representative (ConjClasses.mk p)) p :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (mk_representative (ConjClasses.mk p))
  exact Perm.partition_eq_of_isConj.mp ((alternatingGroup I).subtype.map_isConj hc)

def oddConjugate (t:Perm I)(p:A (I:=I)) : A (I:=I) := (MulAut.conjNormal t) p

theorem odd_conjugate_cover (t:Perm I)(ht:sign t= -1)(p q:A (I:=I))
    (hc:IsConj p.val q.val) : IsConj p q ∨ IsConj (oddConjugate t p) q := by
  obtain ⟨s,hs⟩:=isConj_iff.mp hc
  rcases Int.units_eq_one_or (sign s) with he|he
  · left
    exact isConj_iff.mpr ⟨⟨s,Perm.mem_alternatingGroup.mpr he⟩,Subtype.ext hs⟩
  · right
    have hst:sign (s*t⁻¹)=1 := by rw [map_mul,map_inv,he,ht];norm_num
    apply isConj_iff.mpr
    refine ⟨⟨s*t⁻¹,Perm.mem_alternatingGroup.mpr hst⟩,Subtype.ext ?_⟩
    change (s*t⁻¹)*(t*p.val*t⁻¹)*(s*t⁻¹)⁻¹=q.val
    calc
      _=s*p.val*s⁻¹ := by group
      _=q.val := hs

theorem centralizer_implies_distinct_odd (g:Perm I)
    (hc:Subgroup.centralizer ({g}:Set (Perm I))≤alternatingGroup I) :
    g.partition.parts.Nodup ∧ ∀a∈g.partition.parts,Odd a := by
  obtain ⟨hodd,hfixed,hcount⟩:=Perm.centralizer_le_alternating_iff.mp hc
  have hk:Fintype.card I-g.support.card≤1 := by
    rw [Perm.sum_cycleType] at hfixed
    omega
  have h1:(1:ℕ)∉g.cycleType := by
    intro h
    have ht:=Perm.one_lt_of_mem_cycleType h
    omega
  constructor
  · apply Multiset.nodup_iff_count_le_one.mpr
    intro a
    rw [Perm.parts_partition,Multiset.count_add]
    by_cases ha:a=1
    · subst a
      rw [Multiset.count_eq_zero.mpr h1,Multiset.count_replicate_self,zero_add]
      exact hk
    · simpa only [Multiset.count_replicate,if_neg (Ne.symm ha),add_zero] using hcount a
  · intro a ha
    rw [Perm.parts_partition,Multiset.mem_add] at ha
    rcases ha with ha|ha
    · exact hodd a ha
    · have he:a=1 := Multiset.eq_of_mem_replicate ha
      rw [he]
      decide

theorem nonsplit_isConj (p q:A (I:=I))(he:p.val.partition=q.val.partition)
    (hp:¬(p.val.partition.parts.Nodup ∧ ∀a∈p.val.partition.parts,Odd a)) : IsConj p q := by
  apply CFSGAlternatingOrderThreeConjugacy.isConj_of_odd_centralizer p q
    (Perm.partition_eq_of_isConj.mpr he)
  exact fun hc=>hp (centralizer_implies_distinct_odd p.val hc)

end SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionFibres
