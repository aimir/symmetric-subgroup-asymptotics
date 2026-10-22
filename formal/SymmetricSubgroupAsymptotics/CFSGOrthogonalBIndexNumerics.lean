import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The full-SL-middle skew cell pays the squared ALL-natural-points
index in odd B rank at least three, once the actual centre is trivial.
In particular q=3,r=3 is retained rather than paid by a false factor four. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexNumerics

theorem field_square_lt_units_four (q : ℕ) (hq : 3 ≤ q) : q ^ 2 < (q - 1) ^ 4 := by
  have hsub : q - 1 + 1 = q := by omega
  have hmul : 2 * (q - 1) ≤ (q - 1) * (q - 1) :=
    Nat.mul_le_mul_right _ (by omega : 2 ≤ q - 1)
  have hbase : q < (q - 1) ^ 2 := by nlinarith
  have h := Nat.pow_lt_pow_left hbase (by decide : 2 ≠ 0)
  simpa only [← pow_mul] using h

theorem index_square_lt_of_cell_lower (q r ell G : ℕ) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (hindex : ell * (q - 1) ≤ q ^ (2 * r + 1) - 1)
    (hcell : q ^ (2 * (r * (r - 1))) * (q - 1) ^ (r - 1) ≤ G) : ell ^ 2 < G := by
  have hqpos : 0 < q := by omega
  have he : 4 * r ≤ 2 * (r * (r - 1)) := by
    have h := Nat.mul_le_mul_left r (by omega : 2 ≤ r - 1)
    nlinarith
  have hqpow : q ^ (4 * r) ≤ q ^ (2 * (r * (r - 1))) :=
    Nat.pow_le_pow_right (by omega : 1 ≤ q) he
  have hupow : (q - 1) ^ 4 ≤ (q - 1) ^ (r + 1) :=
    Nat.pow_le_pow_right (by omega : 1 ≤ q - 1) (by omega)
  have hstrict : q ^ (4 * r + 2) < q ^ (2 * (r * (r - 1))) * (q - 1) ^ (r + 1) := by
    calc
      _ = q ^ (4 * r) * q ^ 2 := pow_add _ _ _
      _ < q ^ (4 * r) * (q - 1) ^ 4 :=
        Nat.mul_lt_mul_of_pos_left (field_square_lt_units_four q hq) (pow_pos hqpos _)
      _ ≤ _ := Nat.mul_le_mul hqpow hupow
  have hupper : (ell * (q - 1)) ^ 2 ≤ q ^ (4 * r + 2) := by
    calc
      _ ≤ (q ^ (2 * r + 1)) ^ 2 := Nat.pow_le_pow_left (hindex.trans (Nat.sub_le _ _)) 2
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hlower : q ^ (2 * (r * (r - 1))) * (q - 1) ^ (r + 1) ≤ G * (q - 1) ^ 2 := by
    calc
      _ = (q ^ (2 * (r * (r - 1))) * (q - 1) ^ (r - 1)) * (q - 1) ^ 2 := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ _ := Nat.mul_le_mul_right _ hcell
  apply Nat.lt_of_mul_lt_mul_right
  simpa only [mul_pow] using (hupper.trans_lt hstrict).trans_le hlower

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexNumerics
