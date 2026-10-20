import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryRadicals
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

private theorem small_headCeiling : ∀ i : Fin 47,
  i ≠ 45 → i ≠ 46 → headCeiling i ≤ 2 := by decide +kernel
theorem head_gt_two_states (W : Subrepresentation rho)
    (hW : 2 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    W = states 45 ∨ W = states 46 := by
  obtain ⟨i, rfl⟩ := complete W
  by_cases h45 : i = 45
  · exact Or.inl (congrArg states h45)
  by_cases h46 : i = 46
  · exact Or.inr (congrArg states h46)
  have hb := (coinvariants_finrank_le i).trans (small_headCeiling i h45 h46)
  omega
private theorem kernel45_mem_iff : ∀ v : V,
    v ∈ (charts 45).2.space ↔ v ∈ BinaryRegularEightSquareCarry.K45 := by
  simp only [BinaryRegularEightSquareCarry.K45, BinaryRegularEightSquareCarry.annihilatorSpace,
    Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
private theorem radical45_mem_iff : ∀ v : V,
    v ∈ (radicalCharts 45).2.space ↔ v ∈ BinaryRegularEightSquareCarry.R45 := by
  simp only [BinaryRegularEightSquareCarry.R45, BinaryRegularEightSquareCarry.annihilatorSpace,
    Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem kernel45_space : (states 45).toSubmodule = BinaryRegularEightSquareCarry.K45 := by
  ext v
  exact kernel45_mem_iff v
theorem radical45_space : (radicalCharts 45).2.space = BinaryRegularEightSquareCarry.R45 := by
  ext v
  exact radical45_mem_iff v
private theorem kernel46_mem_iff : ∀ v : V,
    v ∈ (charts 46).2.space ↔ v ∈ BinaryRegularEightSquareCarry.K46 := by
  simp only [BinaryRegularEightSquareCarry.K46, BinaryRegularEightSquareCarry.annihilatorSpace,
    Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
private theorem radical46_mem_iff : ∀ v : V,
    v ∈ (radicalCharts 46).2.space ↔ v ∈ BinaryRegularEightSquareCarry.R46 := by
  simp only [BinaryRegularEightSquareCarry.R46, BinaryRegularEightSquareCarry.annihilatorSpace,
    Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel
theorem kernel46_space : (states 46).toSubmodule = BinaryRegularEightSquareCarry.K46 := by
  ext v
  exact kernel46_mem_iff v
theorem radical46_space : (radicalCharts 46).2.space = BinaryRegularEightSquareCarry.R46 := by
  ext v
  exact radical46_mem_iff v
theorem head_gt_two_kernel_spaces (W : Subrepresentation rho)
    (hW : 2 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    W.toSubmodule = BinaryRegularEightSquareCarry.K45 ∨
      W.toSubmodule = BinaryRegularEightSquareCarry.K46 := by
  rcases head_gt_two_states W hW with rfl | rfl
  · exact Or.inl kernel45_space
  · exact Or.inr kernel46_space

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry
