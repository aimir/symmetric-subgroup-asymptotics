import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
import SymmetricSubgroupAsymptotics.BinaryHeisenbergEightSquareCarryData

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads

private theorem kernel12_mem_iff : ∀ v : V, v ∈ (charts 12).2.space ↔ v ∈ BinaryHeisenbergEightSquareCarry.K12 := by
  simp only [BinaryHeisenbergEightSquareCarry.K12, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem kernel12_space : (states 12).toSubmodule = BinaryHeisenbergEightSquareCarry.K12 := by
  ext v
  exact kernel12_mem_iff v
private theorem radical12_mem_iff : ∀ v : V, v ∈ (radicalCharts 12).2.space ↔ v ∈ BinaryHeisenbergEightSquareCarry.R12 := by
  simp only [BinaryHeisenbergEightSquareCarry.R12, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem radical12_space : (radicalCharts 12).2.space = BinaryHeisenbergEightSquareCarry.R12 := by
  ext v
  exact radical12_mem_iff v
private theorem kernel13_mem_iff : ∀ v : V, v ∈ (charts 13).2.space ↔ v ∈ BinaryHeisenbergEightSquareCarry.K13 := by
  simp only [BinaryHeisenbergEightSquareCarry.K13, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem kernel13_space : (states 13).toSubmodule = BinaryHeisenbergEightSquareCarry.K13 := by
  ext v
  exact kernel13_mem_iff v
private theorem radical13_mem_iff : ∀ v : V, v ∈ (radicalCharts 13).2.space ↔ v ∈ BinaryHeisenbergEightSquareCarry.R13 := by
  simp only [BinaryHeisenbergEightSquareCarry.R13, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem radical13_space : (radicalCharts 13).2.space = BinaryHeisenbergEightSquareCarry.R13 := by
  ext v
  exact radical13_mem_iff v
private theorem kernel14_mem_iff : ∀ v : V, v ∈ (charts 14).2.space ↔ v ∈ BinaryHeisenbergEightSquareCarry.K14 := by
  simp only [BinaryHeisenbergEightSquareCarry.K14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem kernel14_space : (states 14).toSubmodule = BinaryHeisenbergEightSquareCarry.K14 := by
  ext v
  exact kernel14_mem_iff v
private theorem radical14_mem_iff : ∀ v : V, v ∈ (radicalCharts 14).2.space ↔ v ∈ BinaryHeisenbergEightSquareCarry.R14 := by
  simp only [BinaryHeisenbergEightSquareCarry.R14, BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem radical14_space : (radicalCharts 14).2.space = BinaryHeisenbergEightSquareCarry.R14 := by
  ext v
  exact radical14_mem_iff v

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
