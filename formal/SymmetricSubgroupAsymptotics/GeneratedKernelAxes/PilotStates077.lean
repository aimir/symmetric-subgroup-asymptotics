import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_000
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_001
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_002
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_003
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_004
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_005
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_006
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_007
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_008
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_009
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_010
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_011
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_012
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_013
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_014
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_015
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_016
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_017
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.PilotChart077_018

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes077
local instance pilotStatesGroup : Group Source := BinaryTopSource046.group

def charts (i : Fin 19) : Σ d, BinaryCoordinateSpace 8 d :=
  (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then ⟨0,chart0⟩ else ⟨1,chart1⟩) else (if i.val < 3 then ⟨2,chart2⟩ else ⟨2,chart3⟩)) else (if i.val < 6 then (if i.val < 5 then ⟨2,chart4⟩ else ⟨3,chart5⟩) else (if i.val < 7 then ⟨3,chart6⟩ else (if i.val < 8 then ⟨3,chart7⟩ else ⟨4,chart8⟩)))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then ⟨4,chart9⟩ else ⟨4,chart10⟩) else (if i.val < 12 then ⟨4,chart11⟩ else (if i.val < 13 then ⟨4,chart12⟩ else ⟨4,chart13⟩))) else (if i.val < 16 then (if i.val < 15 then ⟨4,chart14⟩ else ⟨5,chart15⟩) else (if i.val < 17 then ⟨5,chart16⟩ else (if i.val < 18 then ⟨5,chart17⟩ else ⟨6,chart18⟩)))))
def states (i : Fin 19) : Subrepresentation action :=
  (if i.val < 9 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then state0 else state1) else (if i.val < 3 then state2 else state3)) else (if i.val < 6 then (if i.val < 5 then state4 else state5) else (if i.val < 7 then state6 else (if i.val < 8 then state7 else state8)))) else (if i.val < 14 then (if i.val < 11 then (if i.val < 10 then state9 else state10) else (if i.val < 12 then state11 else (if i.val < 13 then state12 else state13))) else (if i.val < 16 then (if i.val < 15 then state14 else state15) else (if i.val < 17 then state16 else (if i.val < 18 then state17 else state18)))))

theorem states_space (i : Fin 19) : (states i).toSubmodule=(charts i).2.space := by
  fin_cases i <;> rfl

abbrev kernelChart := chart18
abbrev kernel := state18

end SymmetricSubgroupAsymptotics.BinaryKernelAxes077
