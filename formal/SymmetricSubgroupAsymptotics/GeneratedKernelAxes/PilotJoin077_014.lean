import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotJoinData077_014

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes077
local instance pilotJoinProof014Group : Group Source := BinaryTopSource046.group

namespace PilotJoin014
private theorem old_mem : ∀ a j,
    (charts 14).2.inclusion (Pi.single j 1)∈(charts (child a)).2.space := by decide +kernel
private theorem point_mem : ∀ a,
    kernelChart.inclusion a∈(charts (child a)).2.space := by decide +kernel
private theorem generated : ∀ a j,
    (charts (child a)).2.inclusion (Pi.single j 1)=
      (charts 14).2.inclusion (old a j)+
      ((orbit a j).map (fun g => action g (kernelChart.inclusion a))).sum := by
  simp only [action_numeric]
  decide +kernel
theorem le_kernel_basis : ∀ j,
    (charts 14).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel

theorem child_eq (a : Fin 6 → ZMod 2) :
    (states (child a)).toSubmodule=(states 14).toSubmodule⊔
      binaryOrbitSpan (k := ZMod 2) action (kernelChart.inclusion a) := by
  rw [states_space (child a),states_space 14]
  exact binaryCoordinate_orbit_join_eq (charts 14).2 (charts (child a)).2
    action (states (child a)) (states_space (child a)) (kernelChart.inclusion a)
    (old_mem a) (point_mem a) (old a) (orbit a) (generated a)
end PilotJoin014

end SymmetricSubgroupAsymptotics.BinaryKernelAxes077
