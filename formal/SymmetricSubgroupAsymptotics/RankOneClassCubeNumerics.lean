import SymmetricSubgroupAsymptotics.RankOneSharpOrderCubeNumerics

/-! A polynomial CLASS budget is paid from half-field index fourteen.
This is numerical preparation; no simple-group class bound is assumed
or installed by this file. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.RankOneClassCubeNumerics

theorem class_cube_le (m : ℕ) (hm : 14 ≤ m) : (5*m^2)^3 ≤ 5^(m-1) := by
  have h := RankOneSharpOrderCubeNumerics.polynomial_tail 125 6 5 14 (by decide)
    (by norm_num : (15:ℕ)^6 ≤ 5*14^6)
    (by norm_num : (125:ℕ)*14^6 ≤ 5^13) m hm
  convert h using 1 <;> ring

theorem component_le (q ell classes out : ℕ) (hell : 4 ≤ ell)
    (hq : q ≤ 2*ell) (hc : classes ≤ 2*q+4) (ho : out ≤ ell) :
    classes*out ≤ 5*ell^2 := by
  calc
    classes*out ≤ (2*q+4)*ell := Nat.mul_le_mul hc ho
    _ ≤ (4*ell+4)*ell := Nat.mul_le_mul_right _ (by omega)
    _ ≤ 5*ell^2 := by nlinarith

end SymmetricSubgroupAsymptotics.RankOneClassCubeNumerics
