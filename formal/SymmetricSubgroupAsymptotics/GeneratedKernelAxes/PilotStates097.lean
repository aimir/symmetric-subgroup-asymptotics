import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_000
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_001
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_002
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_003
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_004
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_005
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_006
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_007
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_008
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_009
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_010
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_011
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_012
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_013
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_014
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_015
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart097_016

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes097
local instance pilotStatesGroup : Group Source := BinaryTopSource056.group

def charts (i : Fin 17) : Σ d, BinaryCoordinateSpace 8 d :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ⟨0,chart0⟩ else ⟨1,chart1⟩) else (if i.val < 3 then ⟨2,chart2⟩ else ⟨3,chart3⟩)) else (if i.val < 6 then (if i.val < 5 then ⟨3,chart4⟩ else ⟨3,chart5⟩) else (if i.val < 7 then ⟨4,chart6⟩ else ⟨4,chart7⟩))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then ⟨4,chart8⟩ else ⟨4,chart9⟩) else (if i.val < 11 then ⟨4,chart10⟩ else ⟨4,chart11⟩)) else (if i.val < 14 then (if i.val < 13 then ⟨4,chart12⟩ else ⟨5,chart13⟩) else (if i.val < 15 then ⟨5,chart14⟩ else (if i.val < 16 then ⟨5,chart15⟩ else ⟨6,chart16⟩)))))
def states (i : Fin 17) : Subrepresentation action :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then state0 else state1) else (if i.val < 3 then state2 else state3)) else (if i.val < 6 then (if i.val < 5 then state4 else state5) else (if i.val < 7 then state6 else state7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then state8 else state9) else (if i.val < 11 then state10 else state11)) else (if i.val < 14 then (if i.val < 13 then state12 else state13) else (if i.val < 15 then state14 else (if i.val < 16 then state15 else state16)))))

theorem states_space (i : Fin 17) : (states i).toSubmodule=(charts i).2.space := by
  fin_cases i <;> rfl

abbrev kernelChart := chart16
abbrev kernel := state16

end SymmetricSubgroupAsymptotics.BinaryKernelAxes097
