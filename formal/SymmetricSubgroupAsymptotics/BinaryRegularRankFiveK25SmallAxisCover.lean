import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis23Center
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis13Center
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis16Center
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis17Center
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis19Center
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis20Center
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis21Center
import SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25Axis22Center

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25SmallAxisCover
open BinaryRegularEightNaturalRegistry

theorem envelope (A : Subrepresentation rho)
    (hdim : Module.finrank (ZMod 2) A.toSubmodule ≤ 2) :
    A.toSubmodule=⊥ ∨
      Nat.card {v : V // v ∈ chart25.space ∧ ∀ t : H, rho t v-v ∈ A.toSubmodule} *
        Nat.card {t : H // ∀ v, v ∈ chart25.space → rho t v-v ∈ A.toSubmodule} ≤
          16 * Nat.card A.toSubmodule := by
  obtain ⟨i,rfl⟩ := complete A
  fin_cases i
  · left
    change chart0.space=⊥
    exact le_antisymm (chart0.le_of_basis_mem _ (by intro j; exact Fin.elim0 j)) bot_le
  · change Module.finrank (ZMod 2) chart1.space ≤ 2 at hdim
    rw [chart1.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart2.space ≤ 2 at hdim
    rw [chart2.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart3.space ≤ 2 at hdim
    rw [chart3.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart4.space ≤ 2 at hdim
    rw [chart4.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart5.space ≤ 2 at hdim
    rw [chart5.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart6.space ≤ 2 at hdim
    rw [chart6.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart7.space ≤ 2 at hdim
    rw [chart7.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart8.space ≤ 2 at hdim
    rw [chart8.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart9.space ≤ 2 at hdim
    rw [chart9.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart10.space ≤ 2 at hdim
    rw [chart10.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart11.space ≤ 2 at hdim
    rw [chart11.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart12.space ≤ 2 at hdim
    rw [chart12.finrank] at hdim
    omega
  · exact Or.inr BinaryRegularRankFiveK25Axis13Center.coordinate_capacity
  · change Module.finrank (ZMod 2) chart14.space ≤ 2 at hdim
    rw [chart14.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart15.space ≤ 2 at hdim
    rw [chart15.finrank] at hdim
    omega
  · exact Or.inr BinaryRegularRankFiveK25Axis16Center.coordinate_capacity
  · exact Or.inr BinaryRegularRankFiveK25Axis17Center.coordinate_capacity
  · change Module.finrank (ZMod 2) chart18.space ≤ 2 at hdim
    rw [chart18.finrank] at hdim
    omega
  · exact Or.inr BinaryRegularRankFiveK25Axis19Center.coordinate_capacity
  · exact Or.inr BinaryRegularRankFiveK25Axis20Center.coordinate_capacity
  · exact Or.inr BinaryRegularRankFiveK25Axis21Center.coordinate_capacity
  · exact Or.inr BinaryRegularRankFiveK25Axis22Center.coordinate_capacity
  · exact Or.inr BinaryRegularRankFiveK25Axis23Center.coordinate_capacity
  · change Module.finrank (ZMod 2) chart24.space ≤ 2 at hdim
    rw [chart24.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart25.space ≤ 2 at hdim
    rw [chart25.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart26.space ≤ 2 at hdim
    rw [chart26.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart27.space ≤ 2 at hdim
    rw [chart27.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart28.space ≤ 2 at hdim
    rw [chart28.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart29.space ≤ 2 at hdim
    rw [chart29.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart30.space ≤ 2 at hdim
    rw [chart30.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart31.space ≤ 2 at hdim
    rw [chart31.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart32.space ≤ 2 at hdim
    rw [chart32.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart33.space ≤ 2 at hdim
    rw [chart33.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart34.space ≤ 2 at hdim
    rw [chart34.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart35.space ≤ 2 at hdim
    rw [chart35.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart36.space ≤ 2 at hdim
    rw [chart36.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart37.space ≤ 2 at hdim
    rw [chart37.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart38.space ≤ 2 at hdim
    rw [chart38.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart39.space ≤ 2 at hdim
    rw [chart39.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart40.space ≤ 2 at hdim
    rw [chart40.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart41.space ≤ 2 at hdim
    rw [chart41.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart42.space ≤ 2 at hdim
    rw [chart42.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart43.space ≤ 2 at hdim
    rw [chart43.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart44.space ≤ 2 at hdim
    rw [chart44.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart45.space ≤ 2 at hdim
    rw [chart45.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart46.space ≤ 2 at hdim
    rw [chart46.finrank] at hdim
    omega

end SymmetricSubgroupAsymptotics.BinaryRegularRankFiveK25SmallAxisCover
