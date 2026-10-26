import SymmetricSubgroupAsymptotics.RestrictedPartitionFiniteTableCertificate

/-! A selected finite integer witness. Only the local recurrence and
scalar inequalities are reduced. No partition, composition, group,
or permutation action is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.RestrictedPartitionFiniteSixteenTableData
open RestrictedPartitionFiniteTableCertificate

private def row0 : List ℕ := [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def row1 : List ℕ := [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
private def row2 : List ℕ := [1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9]
private def row3 : List ℕ := [1,1,2,3,4,5,7,8,10,12,14,16,19,21,24,27,30]
private def row4 : List ℕ := [1,1,2,3,5,6,9,11,15,18,23,27,34,39,47,54,64]
private def row5 : List ℕ := [1,1,2,3,5,7,10,13,18,23,30,37,47,57,70,84,101]
private def row6 : List ℕ := [1,1,2,3,5,7,11,14,20,26,35,44,58,71,90,110,136]
private def row7 : List ℕ := [1,1,2,3,5,7,11,15,21,28,38,49,65,82,105,131,164]
private def row8 : List ℕ := [1,1,2,3,5,7,11,15,22,29,40,52,70,89,116,146,186]
private def row9 : List ℕ := [1,1,2,3,5,7,11,15,22,30,41,54,73,94,123,157,201]
private def row10 : List ℕ := [1,1,2,3,5,7,11,15,22,30,42,55,75,97,128,164,212]
private def row11 : List ℕ := [1,1,2,3,5,7,11,15,22,30,42,56,76,99,131,169,219]
private def row12 : List ℕ := [1,1,2,3,5,7,11,15,22,30,42,56,77,100,133,172,224]
private def row13 : List ℕ := [1,1,2,3,5,7,11,15,22,30,42,56,77,101,134,174,227]
private def row14 : List ℕ := [1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,175,229]
private def row15 : List ℕ := [1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,230]
private def row16 : List ℕ := [1,1,2,3,5,7,11,15,22,30,42,56,77,101,135,176,231]

private def rows : List (List ℕ) := [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16]

def entry (n k : ℕ) : ℕ := (rows.getD k []).getD n 0

theorem valid : Valid 16 entry := by
  unfold Valid
  decide +kernel

theorem partition_card_eq_entry (n : ℕ) (hn : n≤16) :
    Nat.card (Nat.Partition n)=entry n n :=
  RestrictedPartitionFiniteTableCertificate.partition_card_eq_entry
    16 entry valid n hn

theorem binary_capacity : ∀ j : Fin 10,
    ((2*entry (j.val+7) (j.val+7)+1)*2^((j.val+7)-1))^3≤
      5^(2*(j.val+7)+1) := by decide +kernel

theorem ternary_capacity : ∀ j : Fin 10,
    (3^((j.val+7)+1)*(2*entry (j.val+7) (j.val+7)))^3≤
      5^(3*(j.val+7)+2) := by decide +kernel

theorem partition_binary_capacity (m : ℕ) (hm : 7 ≤ m) (hmax : m≤16) :
    ((2*Nat.card (Nat.Partition m)+1)*2^(m-1))^3≤5^(2*m+1) := by
  rw [partition_card_eq_entry m hmax]
  have h := binary_capacity ⟨m-7,by omega⟩
  simpa only [Nat.sub_add_cancel hm] using h

theorem partition_ternary_capacity (m : ℕ) (hm : 7 ≤ m) (hmax : m≤16) :
    (3^(m+1)*(2*Nat.card (Nat.Partition m)))^3≤5^(3*m+2) := by
  rw [partition_card_eq_entry m hmax]
  have h := ternary_capacity ⟨m-7,by omega⟩
  simpa only [Nat.sub_add_cancel hm] using h

end SymmetricSubgroupAsymptotics.RestrictedPartitionFiniteSixteenTableData
