import SymmetricSubgroupAsymptotics.ReeFFourOrderCubeTailNumerics

/-! The genuine middle Suzuki Borel index pays the full original Ree
component order cube uniformly from m=2. The induction keeps that same
index, rather than substituting a field-only exponent budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.ReeFFourMiddleSuzukiClassNumerics
open ReeFFourOrderCubeTailNumerics

def indexBound (m : ℕ) : ℕ := (fieldOrder m-1)*2^(m+1)

theorem indexBound_succ_ge_two (m : ℕ) : 2*indexBound m≤indexBound (m+1) := by
  unfold indexBound
  rw [fieldOrder_succ,pow_succ (2 : ℕ) (m+1)]
  calc
    2*((fieldOrder m-1)*2^(m+1))=(fieldOrder m-1)*(2^(m+1)*2) := by ring
    _ ≤ (4*fieldOrder m-1)*(2^(m+1)*2) :=
      Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (by omega : fieldOrder m≤4*fieldOrder m) 1)

theorem index_ge_248 (m : ℕ) (hm : 2 ≤ m) : 248≤indexBound m := by
  have hq : 32≤fieldOrder m :=
    Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega : 5≤2*m+1)
  have hr : 8≤2^(m+1) :=
    Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega : 3≤m+1)
  exact Nat.mul_le_mul (by omega : 31≤fieldOrder m-1) hr

theorem field_power_cube (m : ℕ) (hm : 2 ≤ m) :
    fieldOrder m^81≤5^(indexBound m-1) := by
  induction m, hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    have hb := index_ge_248 m hm
    have hs := indexBound_succ_ge_two m
    calc
      fieldOrder (m+1)^81=(4*fieldOrder m)^81 := by rw [fieldOrder_succ]
      _ = 4^81*fieldOrder m^81 := mul_pow _ _ _
      _ ≤ 5^81*5^(indexBound m-1) := Nat.mul_le_mul
        (Nat.pow_le_pow_left (by decide : (4 : ℕ)≤5) 81) ih
      _ = 5^(81+(indexBound m-1)) := (pow_add _ _ _).symm
      _ ≤ 5^(indexBound (m+1)-1) :=
        Nat.pow_le_pow_right (by decide : 0<(5 : ℕ)) (by omega)

theorem component_order_cube (m : ℕ) (hm : 2 ≤ m) :
    (fieldOrder m^26*(2*m+1))^3≤5^(indexBound m-1) := by
  have hf : 2*m+1≤fieldOrder m := (2*m+1).lt_two_pow_self.le
  calc
    (fieldOrder m^26*(2*m+1))^3≤(fieldOrder m^26*fieldOrder m)^3 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hf) 3
    _ = fieldOrder m^81 := by ring
    _ ≤ _ := field_power_cube m hm

end SymmetricSubgroupAsymptotics.ReeFFourMiddleSuzukiClassNumerics
