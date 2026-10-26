import SymmetricSubgroupAsymptotics.RestrictedPartitionFiniteNinetyNineTableData
import SymmetricSubgroupAsymptotics.PartitionGeometricSmallFibreTail

/-! Checked finite coefficients and the symbolic Euler tail pay every
nonnatural degree n≥m+1 without an index-classification premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.PartitionAllDegreeSmallFibreCapacity

theorem binary_seed (m : ℕ) (hm : 7 ≤ m) :
    ((2*Nat.card (Nat.Partition m)+1)*2^(m-1))^3≤5^(2*m+1) := by
  by_cases h100 : 100≤m
  · exact PartitionGeometricSmallFibreTail.partition_binary_tail m h100
  · exact RestrictedPartitionFiniteNinetyNineTableData.partition_binary_capacity m hm (by omega)

theorem ternary_seed (m : ℕ) (hm : 7 ≤ m) :
    (3^(m+1)*(2*Nat.card (Nat.Partition m)))^3≤5^(3*m+2) := by
  by_cases h100 : 100≤m
  · exact PartitionGeometricSmallFibreTail.partition_ternary_tail m h100
  · exact RestrictedPartitionFiniteNinetyNineTableData.partition_ternary_capacity m hm (by omega)

theorem binary_capacity (m : ℕ) (hm : 7 ≤ m) (n : ℕ) (hn : m+1≤n) :
    ((2*Nat.card (Nat.Partition m)+1)*2^(n-2))^3≤5^(2*n-1) := by
  induction n,hn using Nat.le_induction with
  | base =>
    simpa only [show m+1-2=m-1 by omega,show 2*(m+1)-1=2*m+1 by omega] using binary_seed m hm
  | succ n hn ih =>
    calc
      _=8*((2*Nat.card (Nat.Partition m)+1)*2^(n-2))^3 := by
        rw [show n+1-2=(n-2)+1 by omega,pow_succ]
        ring
      _≤8*5^(2*n-1) := Nat.mul_le_mul_left _ ih
      _≤25*5^(2*n-1) := Nat.mul_le_mul_right _ (by decide : (8:ℕ)≤25)
      _=5^(2*(n+1)-1) := by
        rw [show 2*(n+1)-1=(2*n-1)+2 by omega,pow_add]
        ring

theorem ternary_capacity (m : ℕ) (hm : 7 ≤ m) (n : ℕ) (hn : m+1≤n) :
    (3^n*(2*Nat.card (Nat.Partition m)))^3≤5^(3*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => simpa only [show 3*(m+1)-1=3*m+2 by omega] using ternary_seed m hm
  | succ n hn ih =>
    calc
      _=27*(3^n*(2*Nat.card (Nat.Partition m)))^3 := by rw [pow_succ]; ring
      _≤27*5^(3*n-1) := Nat.mul_le_mul_left _ ih
      _≤125*5^(3*n-1) := Nat.mul_le_mul_right _ (by decide : (27:ℕ)≤125)
      _=5^(3*(n+1)-1) := by
        rw [show 3*(n+1)-1=(3*n-1)+3 by omega,pow_add]
        ring

end SymmetricSubgroupAsymptotics.PartitionAllDegreeSmallFibreCapacity
