import SymmetricSubgroupAsymptotics.Selected1542FirstCenterData
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
set_option maxHeartbeats 1000000 in
theorem firstCenter_orbit : ∀ x : Fin 16, ((firstCenterOrbitWord x).map firstCenterGenerator).prod 0=x := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem firstCenter_candidates : ∀ y : Fin 16,
  (∀ (j : Fin 9) (x : Fin 16), OrbitWordCentralizer.candidate firstCenterGenerator firstCenterOrbitWord y (firstCenterGenerator j x)=firstCenterGenerator j (OrbitWordCentralizer.candidate firstCenterGenerator firstCenterOrbitWord y x)) →
  (∀ x : Fin 16, OrbitWordCentralizer.candidate firstCenterGenerator firstCenterOrbitWord y x=x) ∨
  (∀ x : Fin 16, OrbitWordCentralizer.candidate firstCenterGenerator firstCenterOrbitWord y x=firstCenterZ x) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem firstCenter_cubic : ∀ j : Fin 9, ((firstCenterSourceWord j).map firstCenterCubicLetter).prod=1 := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem firstCenter_z_central : ∀ (j : Fin 3) (x : Fin 16), firstCenterZ (sourceGenerators j x)=sourceGenerators j (firstCenterZ x) := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem firstCenter_z_nontrivial : firstCenterZ 0≠(0 : Fin 16) := by decide +kernel
end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
