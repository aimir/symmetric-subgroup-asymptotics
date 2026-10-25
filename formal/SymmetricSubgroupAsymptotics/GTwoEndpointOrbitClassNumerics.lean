import SymmetricSubgroupAsymptotics.GTwoMiddlePairingClassNumerics

/-! The actual characteristic-three endpoint orbit will have size
`q²-1`. This scalar lemma pays the same original component-order cube
when its proved proper index is `3*(q²-1)`. It supplies no group or orbit
statement and does not cover the field of order three. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.GTwoEndpointOrbitClassNumerics

theorem endpoint_orbit_budget (q : ℕ) (hq : 6 ≤ q) :
    q ^ 60 ≤ 5 ^ (3 * (q ^ 2 - 1) - 1) := by
  have hq2 : 36 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact (GTwoMiddlePairingClassNumerics.quadratic_index_budget q hq).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

end SymmetricSubgroupAsymptotics.GTwoEndpointOrbitClassNumerics
