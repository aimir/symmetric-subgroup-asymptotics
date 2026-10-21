import SymmetricSubgroupAsymptotics.BinaryPairScalarGraphCharts

/-! Literal rows of the original zero model force the scalar graph form
to vanish. The acting elements are constructed in the original subgroup;
no separate action-identification hypothesis remains in these adapters. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

namespace BinaryRegular46GraphHeadRigidity

private theorem generatorTop_original : ∀ i, generatorTop i = 1 ∨
    ∃ j : Fin 3, generatorTop i = BinaryMenuCayley8T3.generators j := by decide +kernel

private theorem generatorOffset_kernel : ∀ i, generatorOffset i ∈ BinaryRegularEightSquareCarry.K46 := by
  simp only [BinaryRegularEightSquareCarry.K46,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

end BinaryRegular46GraphHeadRigidity

namespace BinaryHeisenberg14GraphHeadRigidity

private theorem generatorTop_original : ∀ i, generatorTop i = 1 ∨
    ∃ j : Fin 5, generatorTop i = BinaryMenuCayley8T22.generators j := by decide +kernel

private theorem generatorOffset_kernel : ∀ i, generatorOffset i ∈ BinaryHeisenbergEightSquareCarry.K14 := by
  simp only [BinaryHeisenbergEightSquareCarry.K14,
    BinaryRegularEightSquareCarry.annihilatorSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  decide +kernel

end BinaryHeisenberg14GraphHeadRigidity

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

/-- The original regular template with parity constant layer has the
literal zero graph, including all original source elements and offsets. -/
theorem regular_parity_original_zero_graph
    (hzero : U = F.splitAffineAction)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K46)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hS : (F.pairSumModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (hL : (F.pairConstantModuleLayer W).toSubmodule = (BinaryRegularEightNaturalRegistry.charts 45).2.space)
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryRegular46GraphHeadRigidity.stateChart 0).space := by
  obtain ⟨p,hp⟩ := F.regular_parity_layers_exists_original_graph_chart W hS hL
  have ht (i : Fin 7) : BinaryRegular46GraphHeadRigidity.generatorTop i ∈ F.top.range := by
    rcases BinaryRegular46GraphHeadRigidity.generatorTop_original i with hi | ⟨j,hi⟩
    · rw [hi]
      exact F.top.range.one_mem
    · rw [hi,hH]
      exact Subgroup.subset_closure ⟨j,rfl⟩
  have ha (i : Fin 7) : BinaryRegular46GraphHeadRigidity.generatorOffset i ∈ F.kernelSpace := by
    rw [hK]
    exact BinaryRegular46GraphHeadRigidity.generatorOffset_kernel i
  let u : Fin 7 → U := fun i => F.originalZeroRow hzero
    ⟨BinaryRegular46GraphHeadRigidity.generatorTop i,ht i⟩
    (BinaryRegular46GraphHeadRigidity.generatorOffset i) (ha i)
  have hact (i : Fin 7) : F.originalCoordinateRepresentation (u i) =
      BinaryRegular46GraphHeadRigidity.action i :=
    F.originalCoordinateRepresentation_zeroRow hzero
      ⟨BinaryRegular46GraphHeadRigidity.generatorTop i,ht i⟩ _ (ha i)
  have hhead : 4 ≤ Module.finrank (ZMod 2)
      (F.originalCoordinateSubrepresentation W).toRepresentation.Coinvariants := by
    rwa [← F.originalCoordinateSubrepresentation_head W]
  have he := BinaryRegular46GraphHeadRigidity.form_eq_zero_of_large_head
    F.originalCoordinateRepresentation u (F.originalCoordinateSubrepresentation W) p hp hact hhead
  simpa only [he] using hp

/-- The original Heisenberg template has the same exact zero-graph
conclusion, using its four original selected top involutions. -/
theorem heisenberg_parity_original_zero_graph
    (hzero : U = F.splitAffineAction)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hS : (F.pairSumModuleLayer W).toSubmodule = (BinaryHeisenbergEightNaturalHeads.charts 14).2.space)
    (hL : (F.pairConstantModuleLayer W).toSubmodule = (BinaryHeisenbergEightNaturalHeads.charts 12).2.space)
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (F.originalCoordinateSubrepresentation W).toSubmodule =
      (BinaryHeisenberg14GraphHeadRigidity.stateChart 0).space := by
  obtain ⟨p,hp⟩ := F.heisenberg_parity_layers_exists_original_graph_chart W hS hL
  have ht (i : Fin 7) : BinaryHeisenberg14GraphHeadRigidity.generatorTop i ∈ F.top.range := by
    rcases BinaryHeisenberg14GraphHeadRigidity.generatorTop_original i with hi | ⟨j,hi⟩
    · rw [hi]
      exact F.top.range.one_mem
    · rw [hi,hH]
      exact Subgroup.subset_closure ⟨j,rfl⟩
  have ha (i : Fin 7) : BinaryHeisenberg14GraphHeadRigidity.generatorOffset i ∈ F.kernelSpace := by
    rw [hK]
    exact BinaryHeisenberg14GraphHeadRigidity.generatorOffset_kernel i
  let u : Fin 7 → U := fun i => F.originalZeroRow hzero
    ⟨BinaryHeisenberg14GraphHeadRigidity.generatorTop i,ht i⟩
    (BinaryHeisenberg14GraphHeadRigidity.generatorOffset i) (ha i)
  have hact (i : Fin 7) : F.originalCoordinateRepresentation (u i) =
      BinaryHeisenberg14GraphHeadRigidity.action i :=
    F.originalCoordinateRepresentation_zeroRow hzero
      ⟨BinaryHeisenberg14GraphHeadRigidity.generatorTop i,ht i⟩ _ (ha i)
  have hhead : 4 ≤ Module.finrank (ZMod 2)
      (F.originalCoordinateSubrepresentation W).toRepresentation.Coinvariants := by
    rwa [← F.originalCoordinateSubrepresentation_head W]
  have he := BinaryHeisenberg14GraphHeadRigidity.form_eq_zero_of_large_head
    F.originalCoordinateRepresentation u (F.originalCoordinateSubrepresentation W) p hp hact hhead
  simpa only [he] using hp

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
