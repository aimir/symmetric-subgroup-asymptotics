import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Two literal hyperbolic-frame charts have ample room to pay the
coarse fixed-vector orbit index, even after a centre of order two. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDIndexNumerics

theorem scaled_square_lt (q s ell z : ℕ) (hq : 2 ≤ q) (hz : z ≤ 2)
    (hi : ell ≤ q ^ (2 * (s + 4))) : z * ell ^ 2 < q ^ (8 * s + 20) := by
  have hs : ell ^ 2 ≤ q ^ (4 * s + 16) := by
    have h := Nat.pow_le_pow_left hi 2
    rw [← pow_mul] at h
    convert h using 1 <;> congr 1 <;> omega
  have hg : 4 ≤ q ^ (4 * s + 4) :=
    (Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hp : 0 < q ^ (4 * s + 16) := pow_pos (by omega) _
  calc
    z * ell ^ 2 ≤ 2 * q ^ (4 * s + 16) := Nat.mul_le_mul hz hs
    _ < q ^ (4 * s + 16) * q ^ (4 * s + 4) := by nlinarith
    _ = q ^ (8 * s + 20) := by
      rw [← pow_add]
      congr 1
      omega

theorem square_lt_of_frame_lower (q s ell z N : ℕ) (hq : 2 ≤ q) (hz : z ≤ 2)
    (hi : ell ≤ q ^ (2 * (s + 4))) (hl : q ^ (8 * s + 20) ≤ z * N) :
    ell ^ 2 < N := by
  have h := scaled_square_lt q s ell z hq hz hi
  by_contra hn
  have hN : N ≤ ell ^ 2 := by omega
  exact (not_lt_of_ge (hl.trans (Nat.mul_le_mul_left z hN))) h

end SymmetricSubgroupAsymptotics.CFSGTwistedDIndexNumerics
