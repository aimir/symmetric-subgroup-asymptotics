import SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
import SymmetricSubgroupAsymptotics.Row182QuotientWordGraph
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel

def graphIndex : Fin 9 → Fin 360 := ![237,327,298,286,314,357,281,358,178]

private theorem coordinate_checked : ∀ (j : Fin 9) (x : Fin 6),
    blockFrame.kernelCoordinate 0 (kernelGenerators j) x =
      Row182QuotientWordGraph.sourceState (graphIndex j) x ∧
    blockFrame.kernelCoordinate 1 (kernelGenerators j) x =
      Row182QuotientWordGraph.targetState (graphIndex j) x := by
  decide +kernel

theorem coordinate_zero_injective : Function.Injective (blockFrame.kernelCoordinate 0) := by
  apply Row182QuotientWordGraph.certificate.first_comp_injective_of_generated_states
    blockFrame.twoKernelMap blockFrame.twoKernelMap_injective
    kernelGenerators kernelGenerators_generate
  intro j
  refine ⟨graphIndex j, ?_⟩
  apply Prod.ext
  · apply Equiv.ext
    exact fun x => (coordinate_checked j x).1
  · apply Equiv.ext
    exact fun x => (coordinate_checked j x).2
end SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
