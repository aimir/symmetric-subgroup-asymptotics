import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! One augmented symmetric block cell pays the squared-index bound
at every admissible symplectic rank and field size. These are pure
integer inequalities; actual cell membership is supplied separately. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticCellIndexNumerics

theorem scaled_index_square_lt_cell (q r ell c : ℕ)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hs : r = 2 → q ≠ 2)
    (hc : c ≤ 2) (hc2 : q = 2 → c = 1)
    (hindex : ell * (q - 1) ≤ q ^ (2 * r) - 1) :
    c * ell ^ 2 < q ^ (r * (r + 1) + 1) * (q - 1) := by
  let X := q ^ (2 * r)
  have hX : 0 < X := pow_pos (by omega) _
  by_cases he : q = 2
  · have hr3 : 3 ≤ r := by
      by_contra h
      have hr2 : r = 2 := by omega
      exact hs hr2 he
    have hpoint : ell < X := by simpa [he] using (show ell * (q - 1) < X from by omega)
    have hexp : (2 * r) * 2 ≤ r * (r + 1) + 1 := by nlinarith
    have hp : X ^ 2 ≤ q ^ (r * (r + 1) + 1) := by
      rw [show X ^ 2 = q ^ ((2 * r) * 2) by exact (pow_mul _ _ _).symm]
      exact Nat.pow_le_pow_right (by omega) hexp
    have hsq : ell ^ 2 < X ^ 2 := by nlinarith
    simpa [hc2 he, he] using hsq.trans_le hp
  · have hq3 : 3 ≤ q := by omega
    have hminus : r - 1 + 1 = r := by omega
    have hprod := Nat.mul_le_mul_left (r - 1) (show 3 ≤ r + 1 by omega)
    have hexp : (2 * r) * 2 ≤ (r * (r + 1) + 1) + 1 := by nlinarith
    have hp : X ^ 2 ≤ q ^ (r * (r + 1) + 1) * q := by
      calc
        X ^ 2 = q ^ ((2 * r) * 2) := (pow_mul _ _ _).symm
        _ ≤ q ^ ((r * (r + 1) + 1) + 1) := Nat.pow_le_pow_right (by omega) hexp
        _ = _ := pow_succ _ _
    have hcube : 2 * q ≤ (q - 1) ^ 3 := by
      have hsq : 4 ≤ (q - 1) ^ 2 := by
        have h := Nat.pow_le_pow_left (show 2 ≤ q - 1 by omega) 2
        exact h
      have hm := Nat.mul_le_mul_right (q - 1) hsq
      have hh : 4 * (q - 1) ≤ (q - 1) ^ 3 := by
        simpa only [pow_succ] using hm
      omega
    have hscaled : c * ell ^ 2 * (q - 1) ^ 2 ≤ 2 * (X - 1) ^ 2 := by
      calc
        c * ell ^ 2 * (q - 1) ^ 2 = c * (ell * (q - 1)) ^ 2 := by ring
        _ ≤ 2 * (X - 1) ^ 2 := Nat.mul_le_mul hc (Nat.pow_le_pow_left hindex 2)
    have hstrict : 2 * (X - 1) ^ 2 < 2 * X ^ 2 := by
      have hx : X - 1 + 1 = X := by omega
      nlinarith
    have hcell : 2 * X ^ 2 ≤ q ^ (r * (r + 1) + 1) * (q - 1) ^ 3 := by
      calc
        2 * X ^ 2 ≤ 2 * (q ^ (r * (r + 1) + 1) * q) := Nat.mul_le_mul_left 2 hp
        _ = q ^ (r * (r + 1) + 1) * (2 * q) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hcube
    have hh := (hscaled.trans_lt hstrict).trans_le hcell
    have hrearr : q ^ (r * (r + 1) + 1) * (q - 1) ^ 3 =
        (q ^ (r * (r + 1) + 1) * (q - 1)) * (q - 1) ^ 2 := by ring
    rw [hrearr] at hh
    exact Nat.lt_of_mul_lt_mul_right hh

theorem index_square_lt_of_cell_lower (q r ell c G : ℕ)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hs : r = 2 → q ≠ 2)
    (hc : c ≤ 2) (hc2 : q = 2 → c = 1)
    (hindex : ell * (q - 1) ≤ q ^ (2 * r) - 1)
    (hcell : q ^ (r * (r + 1) + 1) * (q - 1) ≤ c * G) : ell ^ 2 < G := by
  have h := scaled_index_square_lt_cell q r ell c hq hr hs hc hc2 hindex
  by_contra hn
  have hG : G ≤ ell ^ 2 := by omega
  exact (not_lt_of_ge (hcell.trans (Nat.mul_le_mul_left c hG))) h

end SymmetricSubgroupAsymptotics.CFSGSymplecticCellIndexNumerics
