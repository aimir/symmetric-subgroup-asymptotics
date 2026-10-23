import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A distinct-odd partition of degree at least two injects into an
odd-permutation partition of the same degree. Replace one odd part a>=3
by a-1 and 1. The unique even part recovers a, including when a preexisting
part 1 creates a repeated 1. No partition-count formula is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.DistinctOddPartitionInjection

abbrev SplitPartition (n:ℕ) := {p:Nat.Partition n // p.parts.Nodup ∧ ∀a∈p.parts,Odd a}
abbrev OddPartition (n:ℕ) := {p:Nat.Partition n // Odd (n+p.parts.card)}

theorem sum_add_card_even (s:Multiset ℕ)(hs:∀a∈s,Odd a) : Even (s.sum+s.card) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0,rfl⟩
  | @cons a s ih =>
    have ha:Odd a := hs a (Multiset.mem_cons_self _ _)
    have ht:Even (s.sum+s.card) := ih (fun b hb=>hs b (Multiset.mem_cons_of_mem hb))
    have he:Even ((a+1)+(s.sum+s.card)) := (ha.add_odd (by decide : Odd (1:ℕ))).add ht
    simpa only [Multiset.sum_cons,Multiset.card_cons] using
      (show Even (a+s.sum+(s.card+1)) from by convert he using 1; ring)

theorem exists_large_part {n:ℕ}(hn:2≤n)(p:SplitPartition n) : ∃a∈p.val.parts,3≤a := by
  by_contra h
  have hsmall:∀a∈p.val.parts,a=1 := by
    intro a ha
    obtain ⟨k,hk⟩ := p.property.2 a ha
    have hn3:¬3≤a := fun hl=>h ⟨a,ha,hl⟩
    have hpos:=p.val.parts_pos ha
    omega
  have he:p.val.parts=Multiset.replicate p.val.parts.card 1 := Multiset.eq_replicate_card.mpr hsmall
  have hc:=Multiset.nodup_iff_count_le_one.mp p.property.1 1
  rw [he] at hc
  simp only [Multiset.count_replicate_self] at hc
  have hs:=p.val.parts_sum
  rw [he,Multiset.sum_replicate] at hs
  simp only [smul_eq_mul,mul_one] at hs
  omega

def chosenPart {n:ℕ}(hn:2≤n)(p:SplitPartition n) : ℕ := (exists_large_part hn p).choose

theorem chosenPart_mem {n:ℕ}(hn:2≤n)(p:SplitPartition n) : chosenPart hn p∈p.val.parts :=
  (exists_large_part hn p).choose_spec.1

theorem chosenPart_large {n:ℕ}(hn:2≤n)(p:SplitPartition n) : 3≤chosenPart hn p :=
  (exists_large_part hn p).choose_spec.2

def replacePart {n:ℕ}(hn:2≤n)(p:SplitPartition n) : Nat.Partition n where
  parts := (chosenPart hn p-1)::ₘ1::ₘp.val.parts.erase (chosenPart hn p)
  parts_pos := by
    intro a ha
    rcases Multiset.mem_cons.mp ha with he|ht
    · have hl:=chosenPart_large hn p
      omega
    · rcases Multiset.mem_cons.mp ht with he|ht
      · omega
      · exact p.val.parts_pos (Multiset.mem_of_mem_erase ht)
  parts_sum := by
    have hh:=congrArg Multiset.sum (Multiset.cons_erase (chosenPart_mem hn p))
    rw [Multiset.sum_cons,p.val.parts_sum] at hh
    simp only [Multiset.sum_cons]
    have hl:=chosenPart_large hn p
    omega

theorem replacePart_card {n:ℕ}(hn:2≤n)(p:SplitPartition n) :
    (replacePart hn p).parts.card=p.val.parts.card+1 := by
  have hh:=congrArg Multiset.card (Multiset.cons_erase (chosenPart_mem hn p))
  simp only [Multiset.card_cons] at hh
  change ((chosenPart hn p-1)::ₘ1::ₘp.val.parts.erase (chosenPart hn p)).card=_
  simp only [Multiset.card_cons]
  omega

theorem replacePart_odd {n:ℕ}(hn:2≤n)(p:SplitPartition n) :
    Odd (n+(replacePart hn p).parts.card) := by
  have he:Even (n+p.val.parts.card) := by
    have hh:=sum_add_card_even p.val.parts p.property.2
    exact (congrArg (fun t:ℕ=>Even (t+p.val.parts.card)) p.val.parts_sum).mp hh
  rw [replacePart_card]
  have hh:=he.add_odd (by decide : Odd (1:ℕ))
  convert hh using 1 <;> omega

private theorem even_filter {n:ℕ}(hn:2≤n)(p:SplitPartition n) :
    (replacePart hn p).parts.filter Even={chosenPart hn p-1} := by
  have hl:=chosenPart_large hn p
  obtain ⟨k,hk⟩:=p.property.2 (chosenPart hn p) (chosenPart_mem hn p)
  have ha:Even (chosenPart hn p-1) := ⟨k,by omega⟩
  have hr:(p.val.parts.erase (chosenPart hn p)).filter Even=0 :=
    Multiset.filter_eq_nil.mpr (fun a ha=>(Nat.not_even_iff_odd.mpr (p.property.2 a (Multiset.mem_of_mem_erase ha))))
  change ((chosenPart hn p-1)::ₘ1::ₘp.val.parts.erase (chosenPart hn p)).filter Even=_
  rw [Multiset.filter_cons_of_pos _ ha,Multiset.filter_cons_of_neg _ (by decide : ¬Even (1:ℕ)),hr]
  rfl

theorem replacePart_injective {n:ℕ}(hn:2≤n) : Function.Injective (replacePart hn) := by
  intro p q he
  have hp:=even_filter hn p
  have hq:=even_filter hn q
  have hparts:=congrArg Nat.Partition.parts he
  have hfil:=congrArg (Multiset.filter Even) hparts
  rw [hp,hq] at hfil
  have hnum:=congrArg Multiset.sum hfil
  simp only [Multiset.sum_singleton] at hnum
  have hcp:=chosenPart_large hn p
  have hcq:=chosenPart_large hn q
  have ha:chosenPart hn p=chosenPart hn q := by omega
  have herase:=congrArg (fun s:Multiset ℕ=>(s.erase (chosenPart hn p-1)).erase 1) hparts
  change (((chosenPart hn p-1)::ₘ1::ₘp.val.parts.erase (chosenPart hn p)).erase (chosenPart hn p-1)).erase 1 =
    (((chosenPart hn q-1)::ₘ1::ₘq.val.parts.erase (chosenPart hn q)).erase (chosenPart hn p-1)).erase 1 at herase
  rw [ha] at herase
  simp only [Multiset.erase_cons_head] at herase
  apply Subtype.ext
  apply Nat.Partition.ext
  calc
    p.val.parts=chosenPart hn p::ₘp.val.parts.erase (chosenPart hn p) := (Multiset.cons_erase (chosenPart_mem hn p)).symm
    _=chosenPart hn q::ₘq.val.parts.erase (chosenPart hn q) := by rw [ha];exact congrArg (Multiset.cons (chosenPart hn q)) herase
    _=q.val.parts := Multiset.cons_erase (chosenPart_mem hn q)

def toOddPartition {n:ℕ}(hn:2≤n)(p:SplitPartition n) : OddPartition n :=
  ⟨replacePart hn p,replacePart_odd hn p⟩

theorem toOddPartition_injective {n:ℕ}(hn:2≤n) : Function.Injective (toOddPartition hn) :=
  fun _ _ he=>replacePart_injective hn (congrArg Subtype.val he)

end SymmetricSubgroupAsymptotics.DistinctOddPartitionInjection
