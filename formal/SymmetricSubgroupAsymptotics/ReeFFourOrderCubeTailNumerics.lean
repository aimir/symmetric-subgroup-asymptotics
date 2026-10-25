import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! One uniform order-cube tail for the actual Ree F4 field powers.
The seed is q=512 and the parameter step multiplies q by four. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.ReeFFourOrderCubeTailNumerics

def fieldOrder (m : ℕ) : ℕ := 2^(2*m+1)

theorem fieldOrder_succ (m : ℕ) : fieldOrder (m+1)=4*fieldOrder m := by
  have he : 2*(m+1)+1=(2*m+1)+2 := by omega
  unfold fieldOrder
  rw [he,pow_add]
  ring

theorem field_ge_512 (m : ℕ) (hm : 4≤m) : 512≤fieldOrder m :=
  Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega : 9≤2*m+1)

theorem field_power_cube (m : ℕ) (hm : 4≤m) :
    fieldOrder m^81≤5^(fieldOrder m-1) := by
  induction m, hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    have hq := field_ge_512 m hm
    have he : 81≤3*fieldOrder m := by omega
    calc
      fieldOrder (m+1)^81=(4*fieldOrder m)^81 := by rw [fieldOrder_succ]
      _ = 4^81*fieldOrder m^81 := mul_pow _ _ _
      _ ≤ 5^81*5^(fieldOrder m-1) := Nat.mul_le_mul
        (Nat.pow_le_pow_left (by decide : (4 : ℕ)≤5) 81) ih
      _ ≤ 5^(3*fieldOrder m)*5^(fieldOrder m-1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0<(5 : ℕ)) he)
      _ = 5^(fieldOrder (m+1)-1) := by
        rw [←pow_add,fieldOrder_succ]
        congr 1
        omega

theorem component_order_cube (m : ℕ) (hm : 4≤m) :
    (fieldOrder m^26*(2*m+1))^3≤5^(fieldOrder m-1) := by
  have hf : 2*m+1≤fieldOrder m := (2*m+1).lt_two_pow_self.le
  calc
    (fieldOrder m^26*(2*m+1))^3≤(fieldOrder m^26*fieldOrder m)^3 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hf) 3
    _ = fieldOrder m^81 := by ring
    _ ≤ _ := field_power_cube m hm

end SymmetricSubgroupAsymptotics.ReeFFourOrderCubeTailNumerics
