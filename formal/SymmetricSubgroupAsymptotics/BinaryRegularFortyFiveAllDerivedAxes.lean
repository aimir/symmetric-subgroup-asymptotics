import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis0
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis13
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis16
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis17
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis19
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis20
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis21
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis22
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis23
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis38
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis39
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis40
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis41
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis42
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis43
import SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveFixedAxis44

/-! All proper invariant denominators of the actual four-dimensional R45
are covered through the already checked47-state invariant-axis registry.
No original normal subgroup lattice is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveAllDerivedAxes
open BinaryRegularEightNaturalRegistry

theorem coordinate_capacity (A : Subrepresentation rho)
    (hA : A.toSubmodule ≤ BinaryRegularEightSquareCarry.R45)
    (hdim : Module.finrank (ZMod 2) A.toSubmodule ≤ 3) :
    Nat.card {v : V // v ∈ chart45.space ∧ ∀ t : H, rho t v - v ∈ A.toSubmodule} *
      Nat.card {t : H // ∀ v, v ∈ chart45.space → rho t v - v ∈ A.toSubmodule} ≤
      8 * Nat.card A.toSubmodule := by
  obtain ⟨i, rfl⟩ := complete A
  fin_cases i
  · exact BinaryRegularFortyFiveFixedAxis0.coordinate_capacity
  · change Module.finrank (ZMod 2) chart1.space ≤ 3 at hdim
    rw [chart1.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart2.space ≤ 3 at hdim
    rw [chart2.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart3.space ≤ 3 at hdim
    rw [chart3.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart4.space ≤ 3 at hdim
    rw [chart4.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart5.space ≤ 3 at hdim
    rw [chart5.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart6.space ≤ 3 at hdim
    rw [chart6.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart7.space ≤ 3 at hdim
    rw [chart7.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart8.space ≤ 3 at hdim
    rw [chart8.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart9.space ≤ 3 at hdim
    rw [chart9.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart10.space ≤ 3 at hdim
    rw [chart10.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart11.space ≤ 3 at hdim
    rw [chart11.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart12.space ≤ 3 at hdim
    rw [chart12.finrank] at hdim
    omega
  · exact BinaryRegularFortyFiveFixedAxis13.coordinate_capacity
  · change Module.finrank (ZMod 2) chart14.space ≤ 3 at hdim
    rw [chart14.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart15.space ≤ 3 at hdim
    rw [chart15.finrank] at hdim
    omega
  · exact BinaryRegularFortyFiveFixedAxis16.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis17.coordinate_capacity
  · change Module.finrank (ZMod 2) chart18.space ≤ 3 at hdim
    rw [chart18.finrank] at hdim
    omega
  · exact BinaryRegularFortyFiveFixedAxis19.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis20.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis21.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis22.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis23.coordinate_capacity
  · change Module.finrank (ZMod 2) chart24.space ≤ 3 at hdim
    rw [chart24.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart25.space ≤ 3 at hdim
    rw [chart25.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart26.space ≤ 3 at hdim
    rw [chart26.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart27.space ≤ 3 at hdim
    rw [chart27.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart28.space ≤ 3 at hdim
    rw [chart28.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart29.space ≤ 3 at hdim
    rw [chart29.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart30.space ≤ 3 at hdim
    rw [chart30.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart31.space ≤ 3 at hdim
    rw [chart31.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart32.space ≤ 3 at hdim
    rw [chart32.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart33.space ≤ 3 at hdim
    rw [chart33.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart34.space ≤ 3 at hdim
    rw [chart34.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart35.space ≤ 3 at hdim
    rw [chart35.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart36.space ≤ 3 at hdim
    rw [chart36.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart37.space ≤ 3 at hdim
    rw [chart37.finrank] at hdim
    omega
  · exact BinaryRegularFortyFiveFixedAxis38.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis39.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis40.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis41.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis42.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis43.coordinate_capacity
  · exact BinaryRegularFortyFiveFixedAxis44.coordinate_capacity
  · change Module.finrank (ZMod 2) chart45.space ≤ 3 at hdim
    rw [chart45.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart46.space ≤ 3 at hdim
    rw [chart46.finrank] at hdim
    omega

end SymmetricSubgroupAsymptotics.BinaryRegularFortyFiveAllDerivedAxes
