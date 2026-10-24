import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Coupling a normalized central dual orbit with the same subgroup's
exact radical-layer cardinal identity. Separate worst-case indices are
never multiplied. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CentralLayerOrbitCapacityNumerics

theorem normalized_orbit_capacity (p O z v m c w l W : ℕ)
    (hc : 0 < c) (hw : w ≤ W)
    (horbit : p * O * c ≤ z * l)
    (hexact : m * c * w = z * v * l) :
    p * O * v ≤ m * W := by
  have h : (p * O * v) * c ≤ (m * w) * c := by
    calc
      _ = (p * O * c) * v := by ring
      _ ≤ (z * l) * v := Nat.mul_le_mul_right v horbit
      _ = m * c * w := by rw [hexact]; ring
      _ = _ := by ring
  exact (Nat.le_of_mul_le_mul_right h hc).trans (Nat.mul_le_mul_left m hw)

/-- An eight-dimensional binary vector layer, a seven-dimensional
central layer and a four-point normalized dual orbit give index128.
The central intersection is arbitrary; only its literal cardinal is used. -/
theorem binary_eight_seven_index (m c w l : ℕ)
    (hc : 0 < c) (hw : w ≤ 2 ^ 4)
    (horbit : 2 * 4 * c ≤ 2 ^ 7 * l)
    (hexact : m * c * w = 2 ^ 7 * 2 ^ 8 * l) :
    128 ≤ m := by
  have h := normalized_orbit_capacity 2 4 (2 ^ 7) (2 ^ 8)
    m c w l (2 ^ 4) hc hw horbit hexact
  norm_num at h
  omega

end SymmetricSubgroupAsymptotics.CentralLayerOrbitCapacityNumerics
