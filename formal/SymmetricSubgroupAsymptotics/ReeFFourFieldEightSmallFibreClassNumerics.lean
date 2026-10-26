import SymmetricSubgroupAsymptotics.ReeFFourFieldEightClassNumerics

/-! Two raw-component numerical packets for the original q8 factor.
The first retains the proved109 floor; the scaled short-branch packet
is used only at the actual degree at least218. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ReeFFourFieldEightSmallFibreClassNumerics

theorem component_cube_le_five_power (n : ℕ) (hn : 109 ≤ n) :
    ((8 : ℕ)^26*3)^3 ≤ 5^(n+1) :=
  ReeFFourFieldEightClassNumerics.component_order_cube.trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem scaled_component_cube_le_three_power (n : ℕ) (hn : 218 ≤ n) :
    25*((8 : ℕ)^26*3)^3 ≤ 3^n := by
  have hseed : 25*((8 : ℕ)^26*3)^3 ≤ 3^218 := by decide +kernel
  exact hseed.trans (Nat.pow_le_pow_right (by decide) hn)

end SymmetricSubgroupAsymptotics.ReeFFourFieldEightSmallFibreClassNumerics
