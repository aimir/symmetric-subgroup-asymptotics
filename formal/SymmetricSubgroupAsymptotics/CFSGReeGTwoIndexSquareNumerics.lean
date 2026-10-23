import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The two-cell order bound pays the point index even when the full
fixed group has derived index four. This arithmetic uses no group data. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexSquareNumerics

theorem scaled_point_square_lt (q : ℕ) (hq : 9≤q) :
    4*(q^3+1)^2 < q^3*(q-1)*(q^3+1) := by
  have hc : 8≤q^3 := by
    exact Nat.pow_le_pow_left (by omega : 2≤q) 3
  have hm : q^3*8≤q^3*(q-1) :=
    Nat.mul_le_mul_left (q^3) (by omega : 8≤q-1)
  have hs : 4*(q^3+1)<q^3*(q-1) := by omega
  calc
    4*(q^3+1)^2 = (4*(q^3+1))*(q^3+1) := by ring
    _ < q^3*(q-1)*(q^3+1) :=
      Nat.mul_lt_mul_of_pos_right hs (by omega)

theorem index_square_lt (q ell N : ℕ) (hq : 9≤q)
    (hi : ell≤q^3+1) (hN : q^3*(q-1)*(q^3+1)≤4*N) : ell^2<N := by
  have hi2 := Nat.pow_le_pow_left hi 2
  have hscaled := (Nat.mul_le_mul_left 4 hi2).trans_lt
    (scaled_point_square_lt q hq)
  have hlt := hscaled.trans_le hN
  omega

end SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexSquareNumerics
