import SymmetricSubgroupAsymptotics.ComponentOrderCubeWreathExtraGap

/-! A weaker base class cube still leaves the full extra exponent for
at least two factors, once the actual index base is at least five. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.ComponentClassCubeWeakWreathExtraGap

theorem wreath_class_cube_le (A m k : ℕ) (hm : 5 ≤ m) (hk : 2 ≤ k)
    (hA : A^3 ≤ 5^m) : (A^k*k.factorial)^3 ≤ 5^(m^k-2) := by
  induction k, hk using Nat.le_induction with
  | base =>
    calc
      (A^2*Nat.factorial 2)^3 = 8*(A^3)^2 := by
        change (A^2*2)^3=8*(A^3)^2
        ring
      _ ≤ 25*(5^m)^2 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hA 2)
      _ = 5^(2*m+2) := by
        rw [show (25 : ℕ)=5^2 by decide, ← pow_mul, ← pow_add]
        congr 1
        omega
      _ ≤ 5^(m^2-2) := Nat.pow_le_pow_right (by decide) (by
        have hs : m^2-2+2=m^2 := Nat.sub_add_cancel (by nlinarith)
        nlinarith)
  | succ k hk ih =>
    have hmk : k+1 ≤ m^k :=
      (Nat.succ_le_of_lt k.lt_two_pow_self).trans
        (Nat.pow_le_pow_left (by omega : 2 ≤ m) k)
    have hcross : 4*k ≤ (m-1)*(m^k-1) := Nat.mul_le_mul (by omega) (by omega)
    have hexp : (m^k-2)+m+2*k ≤ m^(k+1)-2 := by
      have hxs : m^k-2+2=m^k := Nat.sub_add_cancel (by omega)
      have hxone : m^k-1+1=m^k := Nat.sub_add_cancel (by omega)
      have hms : m-1+1=m := Nat.sub_add_cancel (by omega)
      have hlast : m^(k+1)-2+2=m^(k+1) := Nat.sub_add_cancel (by
        rw [pow_succ]
        exact Nat.mul_le_mul (by omega : 2 ≤ m^k) (by omega : 1 ≤ m))
      rw [pow_succ] at hlast ⊢
      nlinarith
    calc
      (A^(k+1)*(k+1).factorial)^3 =
          (A^k*k.factorial)^3*A^3*(k+1)^3 := by
        rw [pow_succ, Nat.factorial_succ]
        ring
      _ ≤ 5^(m^k-2)*5^m*5^(2*k) := Nat.mul_le_mul (Nat.mul_le_mul ih hA)
        (ComponentOrderCubeWreathNumerics.factorial_step_cube_le k)
      _ = 5^((m^k-2)+m+2*k) := by rw [← pow_add, ← pow_add]
      _ ≤ 5^(m^(k+1)-2) := Nat.pow_le_pow_right (by decide) hexp

end SymmetricSubgroupAsymptotics.ComponentClassCubeWeakWreathExtraGap
