import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_000
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_001
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_002
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_003
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_004
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_005
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_006
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_007
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_008
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_009
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_010
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_011
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_012
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_013
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_014
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_015
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoin097_016

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes097
local instance pilotRegistryGroup : Group Source := BinaryTopSource056.group

private def child (i : Fin 17) (a : Fin 6 → ZMod 2) : Fin 17 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then PilotJoin000.child a else PilotJoin001.child a) else (if i.val < 3 then PilotJoin002.child a else PilotJoin003.child a)) else (if i.val < 6 then (if i.val < 5 then PilotJoin004.child a else PilotJoin005.child a) else (if i.val < 7 then PilotJoin006.child a else PilotJoin007.child a))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then PilotJoin008.child a else PilotJoin009.child a) else (if i.val < 11 then PilotJoin010.child a else PilotJoin011.child a)) else (if i.val < 14 then (if i.val < 13 then PilotJoin012.child a else PilotJoin013.child a) else (if i.val < 15 then PilotJoin014.child a else (if i.val < 16 then PilotJoin015.child a else PilotJoin016.child a)))))
private theorem le_kernel_basis : ∀ i j,
    (charts i).2.inclusion (Pi.single j 1)∈kernelChart.space := by
  intro i
  fin_cases i
  · exact PilotJoin000.le_kernel_basis
  · exact PilotJoin001.le_kernel_basis
  · exact PilotJoin002.le_kernel_basis
  · exact PilotJoin003.le_kernel_basis
  · exact PilotJoin004.le_kernel_basis
  · exact PilotJoin005.le_kernel_basis
  · exact PilotJoin006.le_kernel_basis
  · exact PilotJoin007.le_kernel_basis
  · exact PilotJoin008.le_kernel_basis
  · exact PilotJoin009.le_kernel_basis
  · exact PilotJoin010.le_kernel_basis
  · exact PilotJoin011.le_kernel_basis
  · exact PilotJoin012.le_kernel_basis
  · exact PilotJoin013.le_kernel_basis
  · exact PilotJoin014.le_kernel_basis
  · exact PilotJoin015.le_kernel_basis
  · exact PilotJoin016.le_kernel_basis

private theorem child_eq (i : Fin 17) (a : Fin 6 → ZMod 2) :
    (states (child i a)).toSubmodule=(states i).toSubmodule⊔
      binaryOrbitSpan (k := ZMod 2) action (kernelChart.inclusion a) := by
  fin_cases i
  · exact PilotJoin000.child_eq a
  · exact PilotJoin001.child_eq a
  · exact PilotJoin002.child_eq a
  · exact PilotJoin003.child_eq a
  · exact PilotJoin004.child_eq a
  · exact PilotJoin005.child_eq a
  · exact PilotJoin006.child_eq a
  · exact PilotJoin007.child_eq a
  · exact PilotJoin008.child_eq a
  · exact PilotJoin009.child_eq a
  · exact PilotJoin010.child_eq a
  · exact PilotJoin011.child_eq a
  · exact PilotJoin012.child_eq a
  · exact PilotJoin013.child_eq a
  · exact PilotJoin014.child_eq a
  · exact PilotJoin015.child_eq a
  · exact PilotJoin016.child_eq a

def registry : BinaryInvariantKernelRegistry action kernel states where
  le_kernel i := by
    rw [states_space]
    exact (charts i).2.le_of_basis_mem kernelChart.space (le_kernel_basis i)
  bottom := 0
  bottom_eq := by
    change chart0.space=⊥
    apply le_antisymm
    · apply chart0.le_of_basis_mem
      intro j
      exact Fin.elim0 j
    · exact bot_le
  child i v := child i (kernelChart.coordinates v)
  child_eq i v := by
    have he : kernelChart.inclusion (kernelChart.coordinates v)=(v:Fin 8 → ZMod 2) :=
      (kernelChart.mem_iff v).mp v.property
    exact (child_eq i (kernelChart.coordinates v)).trans (by rw [he])

/-- Every actual invariant subspace of this retained kernel is listed. -/
theorem complete (W : Subrepresentation action) (hW : W.toSubmodule≤kernel.toSubmodule) :
    ∃ i, states i=W := registry.complete W hW

end SymmetricSubgroupAsymptotics.BinaryKernelAxes097
