import SymmetricSubgroupAsymptotics.PartitionGeometricCoefficientBound
import Mathlib.Tactic.Ring

/-! Symbolic small-fibre tails from the actual finite Euler coefficient
bound. The only reductions are two integer seeds at100. Every later
mass is handled by a one-step induction; no partition data is generated
or enumerated by this file. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.PartitionGeometricSmallFibreTail

theorem binary_exponential_comparison (m : ℕ) (hm : 100≤m) :
    192^3*2744^m≤40*3125^m := by
  induction m,hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    calc
      _=2744*(192^3*2744^m) := by rw [pow_succ]; ring
      _≤2744*(40*3125^m) := Nat.mul_le_mul_left _ ih
      _≤3125*(40*3125^m) := Nat.mul_le_mul_right _ (by decide : (2744:ℕ)≤3125)
      _=40*3125^(m+1) := by rw [pow_succ]; ring

theorem ternary_exponential_comparison (m : ℕ) (hm : 100≤m) :
    384^3*9261^m≤25*15625^m := by
  induction m,hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    calc
      _=9261*(384^3*9261^m) := by rw [pow_succ]; ring
      _≤9261*(25*15625^m) := Nat.mul_le_mul_left _ ih
      _≤15625*(25*15625^m) := Nat.mul_le_mul_right _ (by decide : (9261:ℕ)≤15625)
      _=25*15625^(m+1) := by rw [pow_succ]; ring

private theorem power_interchange (a m k : ℕ) : (a^m)^k=(a^k)^m := by
  rw [←pow_mul,Nat.mul_comm m k,pow_mul]

theorem binary_of_coefficient_bound (m p : ℕ) (hm : 100≤m) (hp : 1≤p)
    (hcoef : p*5^m≤64*7^m) :
    ((2*p+1)*2^(m-1))^3≤5^(2*m+1) := by
  have hthree : 2*p+1≤3*p := by omega
  have htwo : (2:ℕ)^m=2^(m-1)*2 := by
    simpa only [Nat.sub_add_cancel (by omega : 1≤m)] using pow_succ (2:ℕ) (m-1)
  have hfive : (5:ℕ)^(3*m)=(5^m)^3 := by
    rw [←pow_mul]
    exact congrArg (fun j : ℕ => (5:ℕ)^j) (Nat.mul_comm 3 m)
  have hfourteen : (14:ℕ)^m=7^m*2^m := by
    simpa only [show (7:ℕ)*2=14 by decide] using mul_pow (7:ℕ) 2 m
  have hscaled : ((2*p+1)*2^(m-1))^3*(8*5^(3*m))≤
      5^(2*m+1)*(8*5^(3*m)) := by
    calc
      _=((2*p+1)*2^m*5^m)^3 := by rw [htwo,hfive]; ring
      _≤((3*p)*2^m*5^m)^3 := Nat.pow_le_pow_left
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hthree)) 3
      _=(3*(p*5^m)*2^m)^3 := by ring
      _≤(3*(64*7^m)*2^m)^3 := Nat.pow_le_pow_left
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hcoef)) 3
      _=(192*14^m)^3 := by rw [hfourteen]; ring
      _=192^3*2744^m := by
        rw [mul_pow,power_interchange 14 m 3,show (14:ℕ)^3=2744 by decide]
      _≤40*3125^m := binary_exponential_comparison m hm
      _=8*(5*5^(5*m)) := by
        have he : (3125:ℕ)^m=5^(5*m) := (pow_mul (5:ℕ) 5 m).symm
        rw [he]
        ring
      _=8*5^(5*m+1) := by rw [pow_succ]; ring
      _=8*(5^(2*m+1)*5^(3*m)) := by
        rw [←pow_add,show (2*m+1)+3*m=5*m+1 by omega]
      _=_ := by ring
  exact Nat.le_of_mul_le_mul_right hscaled
    (Nat.mul_pos (by decide) (pow_pos (by decide) _))

theorem ternary_of_coefficient_bound (m p : ℕ) (hm : 100≤m)
    (hcoef : p*5^m≤64*7^m) :
    (3^(m+1)*(2*p))^3≤5^(3*m+2) := by
  have hfive : (5:ℕ)^(3*m)=(5^m)^3 := by
    rw [←pow_mul]
    exact congrArg (fun j : ℕ => (5:ℕ)^j) (Nat.mul_comm 3 m)
  have htwentyOne : (21:ℕ)^m=3^m*7^m := by
    simpa only [show (3:ℕ)*7=21 by decide] using mul_pow (3:ℕ) 7 m
  have hscaled : (3^(m+1)*(2*p))^3*5^(3*m)≤5^(3*m+2)*5^(3*m) := by
    calc
      _=(3^(m+1)*(2*(p*5^m)))^3 := by rw [hfive]; ring
      _≤(3^(m+1)*(2*(64*7^m)))^3 := Nat.pow_le_pow_left
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hcoef)) 3
      _=(384*21^m)^3 := by rw [pow_succ,htwentyOne]; ring
      _=384^3*9261^m := by
        rw [mul_pow,power_interchange 21 m 3,show (21:ℕ)^3=9261 by decide]
      _≤25*15625^m := ternary_exponential_comparison m hm
      _=25*5^(6*m) := by
        have he : (15625:ℕ)^m=5^(6*m) := (pow_mul (5:ℕ) 6 m).symm
        rw [he]
      _=5^(6*m+2) := by rw [pow_add]; ring
      _=_ := by rw [←pow_add,show (3*m+2)+3*m=6*m+2 by omega]
  exact Nat.le_of_mul_le_mul_right hscaled (pow_pos (by decide) _)

theorem partition_binary_tail (m : ℕ) (hm : 100≤m) :
    ((2*Nat.card (Nat.Partition m)+1)*2^(m-1))^3≤5^(2*m+1) :=
  binary_of_coefficient_bound m (Nat.card (Nat.Partition m)) hm Nat.card_pos
    (PartitionGeometricCoefficientBound.partition_card_mul_five_pow_le m)

theorem partition_ternary_tail (m : ℕ) (hm : 100≤m) :
    (3^(m+1)*(2*Nat.card (Nat.Partition m)))^3≤5^(3*m+2) :=
  ternary_of_coefficient_bound m (Nat.card (Nat.Partition m)) hm
    (PartitionGeometricCoefficientBound.partition_card_mul_five_pow_le m)

end SymmetricSubgroupAsymptotics.PartitionGeometricSmallFibreTail
