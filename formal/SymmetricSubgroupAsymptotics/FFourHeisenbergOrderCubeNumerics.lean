import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! One uniform scalar budget for the actual F4 Heisenberg index at
all field orders at least three. Only the smallest scalar and one
polynomial-to-exponential tail are checked; no action menu is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FFourHeisenbergOrderCubeNumerics

theorem field_power_cube_le (q : ℕ) (hq : 3 ≤ q) :
    q^198 ≤ 5^(2*q^4-1) := by
  by_cases hthree : q=3
  · subst q
    decide +kernel
  · have hq4 : 4 ≤ q := by omega
    have hn : 256 ≤ q^4 := Nat.pow_le_pow_left hq4 4
    have htail := RankOneSharpOrderCubeNumerics.polynomial_tail 1 50 5 256
      (by decide) (by decide +kernel) (by decide +kernel) (q^4) hn
    calc
      q^198 ≤ q^200 := Nat.pow_le_pow_right (by omega) (by decide)
      _ = (q^4)^50 := by rw [←pow_mul]
      _ ≤ 5^(q^4-1) := by simpa only [one_mul] using htail
      _ ≤ 5^(2*q^4-1) := Nat.pow_le_pow_right (by decide)
        (Nat.sub_le_sub_right (by omega) 1)

end SymmetricSubgroupAsymptotics.FFourHeisenbergOrderCubeNumerics
