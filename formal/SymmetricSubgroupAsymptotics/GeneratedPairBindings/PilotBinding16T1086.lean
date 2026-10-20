import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086Schreier
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086Basis

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
local instance pilotAssemblyGroup : Group SourceTop := BinaryTopSource056.group

theorem kernel_space : physicalFrame.kernelSpace=BinaryKernelAxes097.kernelChart.space := by
  apply physicalFrame.kernelSpace_eq_of_schreier BinaryKernelAxes097.kernelChart generators generators_full
    sourceMap sourceMap_kernel sectionMap section_right section_identity
  · intro q j
    change sectionMap q*generators j*(sectionMap (q*sourceMap (generators j)))⁻¹∈_
    rw [sourceMap_generator,nextTop_checked]
    exact physicalFrame.mem_coordinateSubgroup_of_action BinaryKernelAxes097.kernelChart.space
      (schreierElement q j) (schreierBits q j) (schreier_mem q j) (schreier_action q j)
  · intro i
    exact physicalFrame.vector_mem_kernelSpace_of_action (originalWord (basisWords i))
      (BinaryKernelAxes097.kernelChart.inclusion (Pi.single i 1)) (basis_action i)


end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
