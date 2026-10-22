import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A concrete three-parameter alternating block cell pays the squared
natural-point index in every D rank at least four, including q=2,r=4.
The statement is purely arithmetic; actual parameter membership and
projective-point actions are supplied by separate matrix theorems. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNumerics

theorem three_triangle_ge_four_rank_add_two (r t : ℕ) (hr : 4 ≤ r)
    (ht : 2 * t = r * (r - 1)) : 4 * r + 2 ≤ 3 * t := by
  have hminus : r - 1 + 1 = r := by omega
  have hfour : r - 4 + 4 = r := by omega
  nlinarith [Nat.zero_le ((r - 4) ^ 2)]

theorem scaled_index_square_lt_cell (q r t ell c : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r)
    (ht : 2 * t = r * (r - 1)) (hc : c ≤ 4)
    (hindex : ell * (q - 1) ≤ q ^ (2 * r) - 1) : c * ell ^ 2 < q ^ (3 * t) := by
  let X := q ^ (2 * r)
  have hX : 0 < X := pow_pos (by omega) _
  have hqpos : 0 < q := by omega
  have he := three_triangle_ge_four_rank_add_two r t hr ht
  have hp : X ^ 2 * q ^ 2 ≤ q ^ (3 * t) := by
    calc
      X ^ 2 * q ^ 2 = q ^ (4 * r + 2) := by
        rw [show X ^ 2 = q ^ (4 * r) by
          dsimp [X]
          rw [← pow_mul]
          congr 1
          ring, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  have hfour : 4 ≤ q ^ 2 * (q - 1) ^ 2 := by
    have hs : 4 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have hm : 1 ≤ (q - 1) ^ 2 := by
      have h : 1 ≤ q - 1 := by omega
      exact Nat.one_le_pow _ _ h
    nlinarith
  have hscaled : c * ell ^ 2 * (q - 1) ^ 2 ≤ 4 * (X - 1) ^ 2 := by
    calc
      c * ell ^ 2 * (q - 1) ^ 2 = c * (ell * (q - 1)) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul hc (Nat.pow_le_pow_left hindex 2)
  have hstrict : 4 * (X - 1) ^ 2 < 4 * X ^ 2 := by
    have hx : X - 1 + 1 = X := by omega
    nlinarith
  have hbound : 4 * X ^ 2 ≤ q ^ (3 * t) * (q - 1) ^ 2 := by
    calc
      4 * X ^ 2 ≤ (q ^ 2 * (q - 1) ^ 2) * X ^ 2 := Nat.mul_le_mul_right _ hfour
      _ = (X ^ 2 * q ^ 2) * (q - 1) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hp
  exact Nat.lt_of_mul_lt_mul_right ((hscaled.trans_lt hstrict).trans_le hbound)

theorem index_square_lt_of_cell_lower (q r t ell c G : ℕ)
    (hq : 2 ≤ q) (hr : 4 ≤ r) (ht : 2 * t = r * (r - 1)) (hc : c ≤ 4)
    (hindex : ell * (q - 1) ≤ q ^ (2 * r) - 1) (hcell : q ^ (3 * t) ≤ c * G) :
    ell ^ 2 < G := by
  have h := scaled_index_square_lt_cell q r t ell c hq hr ht hc hindex
  by_contra hn
  have hG : G ≤ ell ^ 2 := by omega
  exact (not_lt_of_ge (hcell.trans (Nat.mul_le_mul_left c hG))) h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNumerics
