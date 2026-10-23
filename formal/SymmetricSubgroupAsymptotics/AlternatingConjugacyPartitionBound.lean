import SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionFibreBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Actual alternating conjugacy classes are bounded by ordinary
partitions. Nonsplit even types contribute once; split types contribute
at most once more and inject into odd types by the checked reversible
partition map. No conjugacy-class formula is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionBound
open Equiv Equiv.Perm AlternatingConjugacyPartitionFibres
open AlternatingConjugacyPartitionFibreBounds DistinctOddPartitionInjection

abbrev EvenPartition (n:ℕ) := {p:Nat.Partition n // Even (n+p.parts.card)}

private theorem sum_indicator {T:Type*}[Fintype T](P:T→Prop)[DecidablePred P] :
    (∑t:T,if P t then (1:ℕ) else 0)=Nat.card {t:T // P t} := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [←Finset.sum_filter]
  simp

variable {I:Type*}[Fintype I][DecidableEq I]

theorem class_card_le_even_add_split (t:Perm I)(ht:sign t= -1) :
    Nat.card (ConjClasses (alternatingGroup I))≤
      Nat.card (EvenPartition (Fintype.card I))+Nat.card (SplitPartition (Fintype.card I)) := by
  letI : Finite (alternatingGroup I) :=
    Finite.of_injective (fun g:alternatingGroup I=>g.val) Subtype.val_injective
  letI : Finite (ConjClasses (alternatingGroup I)) :=
    Finite.of_surjective (@ConjClasses.mk (alternatingGroup I) _) ConjClasses.mk_surjective
  letI : Fintype (Nat.Partition (Fintype.card I)) := Fintype.ofFinite _
  letI : ∀p:Nat.Partition (Fintype.card I),Finite (Fibre (I:=I) p) := fun p=>
    Finite.of_injective (fun c:Fibre (I:=I) p=>c.val) Subtype.val_injective
  have hb (p:Nat.Partition (Fintype.card I)) : Nat.card (Fibre (I:=I) p)≤
      (if Even (Fintype.card I+p.parts.card) then 1 else 0)+
      (if p.parts.Nodup ∧ ∀a∈p.parts,Odd a then 1 else 0) := by
    by_cases he:Even (Fintype.card I+p.parts.card)
    · by_cases hs:p.parts.Nodup ∧ ∀a∈p.parts,Odd a
      · simpa only [if_pos he,if_pos hs] using fibre_card_le_two t ht p
      · simpa only [if_pos he,if_neg hs] using fibre_card_le_one (I:=I) p hs
    · letI : IsEmpty (Fibre (I:=I) p) := ⟨fun c=>he (by
        have hh:=partition_even c.val
        simpa only [c.property] using hh)⟩
      have hz:Nat.card (Fibre (I:=I) p)=0 := by simp
      rw [hz,if_neg he,zero_add]
      exact Nat.zero_le _
  have hc:Nat.card (ConjClasses (alternatingGroup I))=
      ∑p:Nat.Partition (Fintype.card I),Nat.card (Fibre (I:=I) p) := by
    calc
      _=Nat.card (Σp:Nat.Partition (Fintype.card I),Fibre (I:=I) p) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv (classPartition (I:=I)))).symm
      _=_ := Nat.card_sigma
  rw [hc]
  calc
    _≤∑p:Nat.Partition (Fintype.card I),
        ((if Even (Fintype.card I+p.parts.card) then 1 else 0)+
          (if p.parts.Nodup ∧ ∀a∈p.parts,Odd a then 1 else 0)) := Finset.sum_le_sum (fun p _=>hb p)
    _=(∑p:Nat.Partition (Fintype.card I),if Even (Fintype.card I+p.parts.card) then 1 else 0)+
        (∑p:Nat.Partition (Fintype.card I),if p.parts.Nodup ∧ ∀a∈p.parts,Odd a then 1 else 0) := Finset.sum_add_distrib
    _=_ := congrArg₂ Nat.add
      (sum_indicator (fun p:Nat.Partition (Fintype.card I)=>Even (Fintype.card I+p.parts.card)))
      (sum_indicator (fun p:Nat.Partition (Fintype.card I)=>p.parts.Nodup ∧ ∀a∈p.parts,Odd a))

theorem even_add_odd_card (n:ℕ) :
    Nat.card (EvenPartition n)+Nat.card (OddPartition n)=Nat.card (Nat.Partition n) := by
  have he:Nat.card (EvenPartition n)+Nat.card {p:Nat.Partition n // ¬Even (n+p.parts.card)}=
      Nat.card (Nat.Partition n) := by
    rw [←Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun p:Nat.Partition n=>Even (n+p.parts.card)))
  have ho:Nat.card {p:Nat.Partition n // ¬Even (n+p.parts.card)}=Nat.card (OddPartition n) :=
    Nat.card_congr
      { toFun := fun p=>⟨p.val,Nat.not_even_iff_odd.mp p.property⟩
        invFun := fun p=>⟨p.val,Nat.not_even_iff_odd.mpr p.property⟩
        left_inv := fun _=>rfl
        right_inv := fun _=>rfl }
  exact ho ▸ he

theorem class_card_le_partitions (hn:2≤Fintype.card I) :
    Nat.card (ConjClasses (alternatingGroup I))≤Nat.card (Nat.Partition (Fintype.card I)) := by
  obtain ⟨a,b,hab⟩:=Fintype.exists_pair_of_one_lt_card (by omega : 1<Fintype.card I)
  have ht:sign (swap a b)= -1 := sign_swap hab
  calc
    _≤Nat.card (EvenPartition (Fintype.card I))+Nat.card (SplitPartition (Fintype.card I)) :=
      class_card_le_even_add_split (swap a b) ht
    _≤Nat.card (EvenPartition (Fintype.card I))+Nat.card (OddPartition (Fintype.card I)) :=
      Nat.add_le_add_left (Nat.card_le_card_of_injective _ (toOddPartition_injective hn)) _
    _=_ := even_add_odd_card _

end SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionBound
