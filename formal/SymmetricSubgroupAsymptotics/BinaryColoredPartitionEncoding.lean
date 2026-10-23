import SymmetricSubgroupAsymptotics.PermutationWreathClassData
import SymmetricSubgroupAsymptotics.BinaryPartitionBudget

/-! Actual positive Bool-colored parts inject into a coupled pair of
ordinary partitions. The two weights sum to the original total n; no
independent product bound discards that constraint. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryColoredPartitionEncoding
open PermutationWreathClassData BinaryPartitionBudget

def parts {n : ℕ} (s : ColoredParts Bool n) (b : Bool) : Multiset ℕ :=
  (s.val.filter (fun t => t.2=b)).map Prod.fst

theorem parts_pos {n : ℕ} (s : ColoredParts Bool n) (b : Bool)
    {m : ℕ} (hm : m∈parts s b) : 0<m := by
  obtain ⟨t,ht,rfl⟩ := Multiset.mem_map.mp hm
  exact s.property.1 t (Multiset.mem_of_mem_filter ht)

theorem recolor_filter {n : ℕ} (s : ColoredParts Bool n) (b : Bool) :
    (parts s b).map (fun m => (m,b))=s.val.filter (fun t => t.2=b) := by
  rw [parts,Multiset.map_map]
  calc
    _=(s.val.filter (fun t => t.2=b)).map id := by
      apply Multiset.map_congr rfl
      intro t ht
      apply Prod.ext
      · rfl
      · exact (Multiset.of_mem_filter ht).symm
    _=s.val.filter (fun t => t.2=b) := Multiset.map_id _

private theorem filter_split (s : Multiset (ℕ × Bool)) :
    s.filter (fun t => t.2=false)+s.filter (fun t => t.2=true)=s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons t s ih => cases h : t.2 <;> simp [h,ih]

theorem reconstruction {n : ℕ} (s : ColoredParts Bool n) :
    (parts s false).map (fun m => (m,false))+
      (parts s true).map (fun m => (m,true))=s.val := by
  rw [recolor_filter,recolor_filter]
  exact filter_split s.val

theorem sum_parts {n : ℕ} (s : ColoredParts Bool n) :
    (parts s false).sum+(parts s true).sum=n := by
  have h := congrArg (fun m : Multiset (ℕ × Bool) => (m.map Prod.fst).sum)
    (reconstruction s)
  have he : (parts s false).sum+(parts s true).sum=(s.val.map Prod.fst).sum := by
    simpa only [Multiset.map_add,Multiset.sum_add,Multiset.map_map,
      Function.comp_def,Multiset.map_id'] using h
  exact he.trans s.property.2

def pairedEncoding {n : ℕ} (s : ColoredParts Bool n) : PairedPartitions n := by
  let k := (parts s false).sum
  have hk : k<n+1 := by have h := sum_parts s; dsimp only [k]; omega
  exact ⟨⟨k,hk⟩,
    ⟨{parts:=parts s false,parts_pos:=fun hm => parts_pos s false hm,parts_sum:=rfl},
     {parts:=parts s true,parts_pos:=fun hm => parts_pos s true hm,
      parts_sum:=by have h := sum_parts s; dsimp only [k]; omega}⟩⟩

theorem pairedEncoding_injective (n : ℕ) : Function.Injective
    (pairedEncoding : ColoredParts Bool n → PairedPartitions n) := by
  intro s t he
  have hf : parts s false=parts t false :=
    congrArg (fun p : PairedPartitions n => p.2.1.parts) he
  have ht : parts s true=parts t true :=
    congrArg (fun p : PairedPartitions n => p.2.2.parts) he
  apply Subtype.ext
  calc
    s.val=(parts s false).map (fun m => (m,false))+
        (parts s true).map (fun m => (m,true)) := (reconstruction s).symm
    _=(parts t false).map (fun m => (m,false))+
        (parts t true).map (fun m => (m,true)) := by rw [hf,ht]
    _=t.val := reconstruction t

end SymmetricSubgroupAsymptotics.BinaryColoredPartitionEncoding
