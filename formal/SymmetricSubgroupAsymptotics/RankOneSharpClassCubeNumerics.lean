import SymmetricSubgroupAsymptotics.RankOneClassCubeNumerics
import Mathlib.Data.Nat.Prime.Basic

/-! The sharper trace count pays the same half-field component budget
already from field order seventeen. The small interval is treated by
prime-power arithmetic, not a list of primitive actions. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.RankOneSharpClassCubeNumerics

theorem class_cube_le (m : ℕ) (hm : 12 ≤ m) : ((2*m+4)*m)^3 ≤ 5^(m-1) := by
  by_cases hbase : m=12
  · subst m; decide
  · have hm13 : 13 ≤ m := by omega
    have h := RankOneSharpOrderCubeNumerics.polynomial_tail 27 6 5 13 (by decide)
      (by norm_num : (14:ℕ)^6 ≤ 5*13^6)
      (by norm_num : (27:ℕ)*13^6 ≤ 5^12) m hm13
    have hc : (2*m+4)*m ≤ 3*m^2 := by nlinarith
    exact (Nat.pow_le_pow_left hc 3).trans (by convert h using 1; ring)

theorem exponent_one_of_small_order (p e : ℕ) (hp : p.Prime) (he : 0<e)
    (hlo : 17 ≤ p^e) (hhi : p^e ≤ 22) : e=1 := by
  by_contra hne
  have he2 : 2 ≤ e := by omega
  have he5 : e<5 := by
    by_contra h
    have hb := (Nat.pow_le_pow_left hp.two_le 5).trans
      (Nat.pow_le_pow_right hp.pos (by omega : 5 ≤ e))
    norm_num at hb
    omega
  have hp5 : p<5 := by
    by_contra h
    have hb := (Nat.pow_le_pow_left (by omega : 5 ≤ p) 2).trans
      (Nat.pow_le_pow_right hp.pos he2)
    norm_num at hb
    omega
  have hp2 := hp.two_le
  have hpne : p ≠ 4 := by
    intro h
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp
  have hp23 : p=2 ∨ p=3 := by omega
  rcases hp23 with rfl | rfl
  · have hb := Nat.pow_le_pow_right (by decide : 0<2) (by omega : e ≤ 4)
    norm_num at hb
    omega
  · by_cases he3 : 3 ≤ e
    · have hb := Nat.pow_le_pow_right (by decide : 0<3) he3
      norm_num at hb
      omega
    · have htwo : e=2 := by omega
      subst e
      norm_num at hlo

end SymmetricSubgroupAsymptotics.RankOneSharpClassCubeNumerics
