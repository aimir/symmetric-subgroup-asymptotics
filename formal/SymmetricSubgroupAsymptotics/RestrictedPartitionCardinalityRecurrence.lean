import SymmetricSubgroupAsymptotics.PartitionFibonacciBound

/-! Exact restricted-partition recurrence by removing one occurrence
of the largest allowed part. The natural-number program counts via
this recurrence, not by enumerating partitions or compositions. Only
the selected mass-sixteen reduction is included in this first pilot. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.RestrictedPartitionCardinalityRecurrence

abbrev Restricted (n k : ℕ) := {p : Nat.Partition n // ∀ i∈p.parts,i≤k}

private abbrev HasLargest (n k : ℕ) := {p : Restricted n k // k∈p.val.parts}
private abbrev NoLargest (n k : ℕ) := {p : Restricted n k // k∉p.val.parts}

private noncomputable def noLargestEquiv (n k : ℕ) :
    NoLargest n (k+1) ≃ Restricted n k where
  toFun p := ⟨p.val.val,by
    intro i hi
    have hb := p.val.property i hi
    have hne : i≠k+1 := fun he => p.property (he ▸ hi)
    omega⟩
  invFun p := ⟨⟨p.val,fun i hi => (p.property i hi).trans (by omega)⟩,by
    intro hi
    have hb := p.property (k+1) hi
    omega⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

private noncomputable def hasLargestEquiv (n k : ℕ) :
    HasLargest (n+(k+1)) (k+1) ≃ Restricted n (k+1) where
  toFun p := ⟨{
    parts := p.val.val.parts.erase (k+1)
    parts_pos := fun hi => p.val.val.parts_pos (Multiset.mem_of_mem_erase hi)
    parts_sum := by
      have hh := congrArg Multiset.sum (Multiset.cons_erase p.property)
      rw [Multiset.sum_cons,p.val.val.parts_sum] at hh
      omega },fun i hi => p.val.property i (Multiset.mem_of_mem_erase hi)⟩
  invFun p := ⟨⟨{
    parts := (k+1) ::ₘ p.val.parts
    parts_pos := by
      intro i hi
      rcases Multiset.mem_cons.mp hi with rfl|hi
      · omega
      · exact p.val.parts_pos hi
    parts_sum := by rw [Multiset.sum_cons,p.val.parts_sum,Nat.add_comm] },by
      intro i hi
      rcases Multiset.mem_cons.mp hi with rfl|hi
      · exact le_rfl
      · exact p.property i hi⟩,Multiset.mem_cons_self _ _⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Nat.Partition.ext
    exact Multiset.cons_erase p.property
  right_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact Multiset.erase_cons_head _ _

private noncomputable def lowerEquiv (n k : ℕ) (hn : n≤k) :
    Restricted n (k+1) ≃ Restricted n k where
  toFun p := ⟨p.val,fun _ hi => (Nat.Partition.le_of_mem_parts hi).trans hn⟩
  invFun p := ⟨p.val,fun i hi => (p.property i hi).trans (by omega)⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl

private theorem card_zero (k : ℕ) : Nat.card (Restricted 0 k)=1 := by
  letI : Unique (Restricted 0 k) := {
    default := ⟨default,by
      intro i hi
      have hh := Nat.Partition.le_of_mem_parts hi
      omega⟩
    uniq := fun p => Subtype.ext (Subsingleton.elim _ _) }
  exact Nat.card_unique

private theorem card_zero_bound (n : ℕ) : Nat.card (Restricted (n+1) 0)=0 := by
  letI : IsEmpty (Restricted (n+1) 0) := ⟨by
    intro p
    have he : p.val.parts=0 := Multiset.eq_zero_of_forall_notMem (by
      intro i hi
      have hp := p.val.parts_pos hi
      have hb := p.property i hi
      omega)
    have hs := p.val.parts_sum
    rw [he,Multiset.sum_zero] at hs
    omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private theorem card_add_largest (n k : ℕ) :
    Nat.card (Restricted (n+(k+1)) (k+1))=
      Nat.card (Restricted (n+(k+1)) k)+Nat.card (Restricted n (k+1)) := by
  classical
  have hsplit : Nat.card (Restricted (n+(k+1)) (k+1))=
      Nat.card (HasLargest (n+(k+1)) (k+1))+
        Nat.card (NoLargest (n+(k+1)) (k+1)) := by
    rw [←Nat.card_sum]
    exact (Nat.card_congr (Equiv.sumCompl
      (fun p : Restricted (n+(k+1)) (k+1) => k+1∈p.val.parts))).symm
  rw [hsplit,Nat.card_congr (hasLargestEquiv n k),
    Nat.card_congr (noLargestEquiv (n+(k+1)) k),Nat.add_comm]

theorem card_recurrence (n k : ℕ) :
    Nat.card (Restricted n (k+1))=Nat.card (Restricted n k)+
      (if k+1≤n then Nat.card (Restricted (n-(k+1)) (k+1)) else 0) := by
  by_cases h : k+1≤n
  · rw [if_pos h]
    have hh := card_add_largest (n-(k+1)) k
    simpa only [Nat.sub_add_cancel h] using hh
  · rw [if_neg h,Nat.add_zero]
    exact Nat.card_congr (lowerEquiv n k (by omega))

def count : ℕ → ℕ → ℕ
  | 0,_ => 1
  | n+1,0 => 0
  | n+1,k+1 => count (n+1) k+
      if h : k+1≤n+1 then count ((n+1)-(k+1)) (k+1) else 0
termination_by n k => n+k
decreasing_by all_goals omega

theorem card_eq_count (n k : ℕ) : Nat.card (Restricted n k)=count n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ihn =>
    cases n with
    | zero => simpa only [count] using card_zero k
    | succ n =>
      induction k with
      | zero => simpa only [count] using card_zero_bound n
      | succ k ihk =>
        rw [card_recurrence,count,ihk]
        split_ifs with h
        · rw [ihn ((n+1)-(k+1)) (by omega) (k+1)]
        · rfl

private def allEquiv (n : ℕ) : Restricted n n ≃ Nat.Partition n where
  toFun p := p.val
  invFun p := ⟨p,fun _ hi => Nat.Partition.le_of_mem_parts hi⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := rfl

theorem partition_card_eq_count (n : ℕ) : Nat.card (Nat.Partition n)=count n n :=
  (Nat.card_congr (allEquiv n)).symm.trans (card_eq_count n n)

theorem partition_sixteen_card : Nat.card (Nat.Partition 16)=231 :=
  (partition_card_eq_count 16).trans (by decide +kernel)

end SymmetricSubgroupAsymptotics.RestrictedPartitionCardinalityRecurrence
