import SymmetricSubgroupAsymptotics.FiniteColoredPartitionTuple
import SymmetricSubgroupAsymptotics.PermutationWreathClassData
import Mathlib.Data.Multiset.Filter

/-! Split one color from a positive colored partition, retaining its
literal weight and the complementary total. The two pieces reconstruct
the original multiset, including every multiplicity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteColoredPartitionSplit

abbrev Parts (k n : ℕ) := PermutationWreathClassData.ColoredParts (Fin k) n

def removeHead {k : ℕ} (t : ℕ × Fin (k+1)) : Option (ℕ × Fin k) :=
  Fin.cases none (fun c => some (t.1,c)) t.2

def headParts {k : ℕ} (s : Multiset (ℕ × Fin (k+1))) : Multiset ℕ :=
  (s.filter (fun t => t.2=0)).map Prod.fst

def tailParts {k : ℕ} (s : Multiset (ℕ × Fin (k+1))) : Multiset (ℕ × Fin k) :=
  s.filterMap removeHead

theorem head_zero_cons {k : ℕ} (m : ℕ) (s : Multiset (ℕ × Fin (k+1))) :
    headParts ((m,0) ::ₘ s) = m ::ₘ headParts s := by simp [headParts]

theorem head_succ_cons {k : ℕ} (m : ℕ) (c : Fin k)
    (s : Multiset (ℕ × Fin (k+1))) :
    headParts ((m,c.succ) ::ₘ s) = headParts s := by simp [headParts]

theorem tail_zero_cons {k : ℕ} (m : ℕ) (s : Multiset (ℕ × Fin (k+1))) :
    tailParts ((m,0) ::ₘ s) = tailParts s := by
  simp [tailParts,removeHead]

theorem tail_succ_cons {k : ℕ} (m : ℕ) (c : Fin k)
    (s : Multiset (ℕ × Fin (k+1))) :
    tailParts ((m,c.succ) ::ₘ s) = (m,c) ::ₘ tailParts s := by
  simp [tailParts,removeHead]

theorem reconstruction {k : ℕ} (s : Multiset (ℕ × Fin (k+1))) :
    (headParts s).map (fun m => (m,(0 : Fin (k+1)))) +
      (tailParts s).map (fun t => (t.1,t.2.succ)) = s := by
  induction s using Multiset.induction_on with
  | empty => simp [headParts,tailParts]
  | cons t s ih =>
    rcases t with ⟨m,c⟩
    refine Fin.cases ?_ (fun c => ?_) c
    · simp only [head_zero_cons,tail_zero_cons,Multiset.map_cons,Multiset.cons_add,ih]
    · simp only [head_succ_cons,tail_succ_cons,Multiset.map_cons,Multiset.add_cons,ih]

theorem head_positive {k n : ℕ} (s : Parts (k+1) n)
    {m : ℕ} (hm : m ∈ headParts s.val) : 0 < m := by
  obtain ⟨t,ht,rfl⟩ := Multiset.mem_map.mp hm
  exact s.property.1 t (Multiset.mem_of_mem_filter ht)

theorem tail_positive {k n : ℕ} (s : Parts (k+1) n)
    {t : ℕ × Fin k} (ht : t ∈ tailParts s.val) : 0 < t.1 := by
  obtain ⟨⟨m,c⟩,hmem,he⟩ := (Multiset.mem_filterMap removeHead s.val).mp ht
  revert hmem he
  refine Fin.cases ?_ (fun c => ?_) c
  · intro _ he
    simp only [removeHead,Fin.cases_zero] at he
    cases he
  · intro hmem he
    have he' : (m,c) = t := Option.some.inj he
    have hm := s.property.1 (m,c.succ) hmem
    have hem : m = t.1 := congrArg Prod.fst he'
    simpa only [hem] using hm

theorem weight_sum {k n : ℕ} (s : Parts (k+1) n) :
    (headParts s.val).sum + ((tailParts s.val).map Prod.fst).sum = n := by
  have h := congrArg (fun t : Multiset (ℕ × Fin (k+1)) => (t.map Prod.fst).sum)
    (reconstruction s.val)
  have he : (headParts s.val).sum + ((tailParts s.val).map Prod.fst).sum =
      (s.val.map Prod.fst).sum := by
    simpa only [Multiset.map_add,Multiset.sum_add,Multiset.map_map,
      Function.comp_def,Multiset.map_id'] using h
  exact he.trans s.property.2

def headIndex {k n : ℕ} (s : Parts (k+1) n) : Fin (n+1) :=
  ⟨(headParts s.val).sum,by have h := weight_sum s; omega⟩

def headPartition {k n : ℕ} (s : Parts (k+1) n) :
    Nat.Partition (headIndex s).val where
  parts := headParts s.val
  parts_pos := fun hm => head_positive s hm
  parts_sum := rfl

def tailState {k n : ℕ} (s : Parts (k+1) n) : Parts k (n-(headIndex s).val) :=
  ⟨tailParts s.val,fun _ ht => tail_positive s ht,by
    have h := weight_sum s
    change ((tailParts s.val).map Prod.fst).sum = n-(headParts s.val).sum
    omega⟩

theorem zero_empty {n : ℕ} (s : Parts 0 n) : s.val = 0 := by
  apply Multiset.eq_zero_of_forall_notMem
  rintro ⟨m,c⟩ _
  exact Fin.elim0 c

theorem zero_weight {n : ℕ} (s : Parts 0 n) : n = 0 := by
  have h := s.property.2
  simpa only [zero_empty s,Multiset.map_zero,Multiset.sum_zero] using h.symm

end SymmetricSubgroupAsymptotics.FiniteColoredPartitionSplit
