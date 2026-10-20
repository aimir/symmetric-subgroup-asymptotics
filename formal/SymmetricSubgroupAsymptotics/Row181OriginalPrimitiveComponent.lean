import SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
import SymmetricSubgroupAsymptotics.CyclicPointStabilizerPrimitivity
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
abbrev component := (blockFrame.kernelCoordinate 0).range

def componentGenerator (j : Fin 9) : component :=
  ⟨blockFrame.kernelCoordinate 0 (kernelGenerators j), ⟨kernelGenerators j, rfl⟩⟩

private theorem cycle_fixed : componentGenerator 1 • (5 : Fin 6) = 5 := by decide +kernel
private theorem cycle_cover : ∀ x : Fin 6, x ≠ 5 →
    ∃ n : Fin 5, componentGenerator 1 ^ n.val • (0 : Fin 6) = x := by decide +kernel

instance component_primitive : MulAction.IsPreprimitive component (Fin 6) := by
  apply primitive_of_cyclic_stabilizer_and_mover
    (componentGenerator 1) (componentGenerator 0) (5 : Fin 6) (0 : Fin 6) cycle_fixed
  · intro x hx
    obtain ⟨n,hn⟩ := cycle_cover x hx
    exact ⟨n.val,hn⟩
  · decide +kernel
end SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
