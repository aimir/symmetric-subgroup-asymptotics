import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNumerics

/-! The D cell has enough spare powers of q that even a centre bound
by q squared suffices. Actual scalar recognition gives the stronger
bound by q, so no new form calculation is needed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexScalarNumerics
open CFSGOrthogonalDIndexNumerics

theorem scaled_index_square_lt_cell (q r t ell c : ℕ) (hq : 2 ≤ q) (hr : 4 ≤ r)
    (ht : 2 * t = r * (r - 1)) (hc : c ≤ q ^ 2)
    (hindex : ell * (q - 1) ≤ q ^ (2 * r) - 1) : c * ell ^ 2 < q ^ (3 * t) := by
  let X := q ^ (2 * r)
  have hX : 0 < X := pow_pos (by omega) _
  have he := three_triangle_ge_four_rank_add_two r t hr ht
  have hp : q ^ 2 * X ^ 2 ≤ q ^ (3 * t) := by
    calc
      q ^ 2 * X ^ 2 = q ^ (4 * r + 2) := by
        rw [show X ^ 2 = q ^ (4 * r) by
          dsimp [X]
          rw [← pow_mul]
          congr 1
          ring, ← pow_add]
        congr 1
        omega
      _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  have hscaled : c * ell ^ 2 * (q - 1) ^ 2 ≤ q ^ 2 * (X - 1) ^ 2 := by
    calc
      c * ell ^ 2 * (q - 1) ^ 2 = c * (ell * (q - 1)) ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul hc (Nat.pow_le_pow_left hindex 2)
  have hstrict : q ^ 2 * (X - 1) ^ 2 < q ^ 2 * X ^ 2 := by
    have hx : X - 1 + 1 = X := by omega
    apply Nat.mul_lt_mul_of_pos_left _ (pow_pos (by omega) _)
    nlinarith
  have hm : 1 ≤ (q - 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hbound : q ^ 2 * X ^ 2 ≤ q ^ (3 * t) * (q - 1) ^ 2 := by
    exact hp.trans (by simpa only [mul_one] using Nat.mul_le_mul_left (q ^ (3 * t)) hm)
  exact Nat.lt_of_mul_lt_mul_right ((hscaled.trans_lt hstrict).trans_le hbound)

theorem index_square_lt_of_cell_lower (q r t ell c G : ℕ)
    (hq : 2 ≤ q) (hr : 4 ≤ r) (ht : 2 * t = r * (r - 1)) (hc : c ≤ q ^ 2)
    (hindex : ell * (q - 1) ≤ q ^ (2 * r) - 1) (hcell : q ^ (3 * t) ≤ c * G) :
    ell ^ 2 < G := by
  have h := scaled_index_square_lt_cell q r t ell c hq hr ht hc hindex
  by_contra hn
  have hG : G ≤ ell ^ 2 := by omega
  exact (not_lt_of_ge (hcell.trans (Nat.mul_le_mul_left c hG))) h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexScalarNumerics
