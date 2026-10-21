import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads

/-! All invariant axes of dimension at most three lie in the same
original four-dimensional radical. The complete47-state linear registry
is used; no subgroup or extension-class census is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

theorem small_axis_le_R45 (A : Subrepresentation rho)
    (hdim : Module.finrank (ZMod 2) A.toSubmodule ≤ 3) :
    A.toSubmodule ≤ BinaryRegularEightSquareCarry.R45 := by
  rw [←radical45_space]
  change A.toSubmodule ≤ chart46.space
  obtain ⟨i,rfl⟩ := complete A
  fin_cases i
  · exact chart0.le_of_basis_mem _ (by decide +kernel)
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
  · exact chart13.le_of_basis_mem _ (by decide +kernel)
  · change Module.finrank (ZMod 2) chart14.space ≤ 3 at hdim
    rw [chart14.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart15.space ≤ 3 at hdim
    rw [chart15.finrank] at hdim
    omega
  · exact chart16.le_of_basis_mem _ (by decide +kernel)
  · exact chart17.le_of_basis_mem _ (by decide +kernel)
  · change Module.finrank (ZMod 2) chart18.space ≤ 3 at hdim
    rw [chart18.finrank] at hdim
    omega
  · exact chart19.le_of_basis_mem _ (by decide +kernel)
  · exact chart20.le_of_basis_mem _ (by decide +kernel)
  · exact chart21.le_of_basis_mem _ (by decide +kernel)
  · exact chart22.le_of_basis_mem _ (by decide +kernel)
  · exact chart23.le_of_basis_mem _ (by decide +kernel)
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
  · exact chart38.le_of_basis_mem _ (by decide +kernel)
  · exact chart39.le_of_basis_mem _ (by decide +kernel)
  · exact chart40.le_of_basis_mem _ (by decide +kernel)
  · exact chart41.le_of_basis_mem _ (by decide +kernel)
  · exact chart42.le_of_basis_mem _ (by decide +kernel)
  · exact chart43.le_of_basis_mem _ (by decide +kernel)
  · exact chart44.le_of_basis_mem _ (by decide +kernel)
  · change Module.finrank (ZMod 2) chart45.space ≤ 3 at hdim
    rw [chart45.finrank] at hdim
    omega
  · change Module.finrank (ZMod 2) chart46.space ≤ 3 at hdim
    rw [chart46.finrank] at hdim
    omega

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry
