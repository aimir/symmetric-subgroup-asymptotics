import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1098Base

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
local instance pilotBasisGroup : Group SourceTop := BinaryTopSource046.group

def basisWords (i : Fin 6) : List (Fin 5) := (if i.val < 3 then (if i.val < 1 then [1] else (if i.val < 2 then [3,3,4,0,4,4,4,4,4,4,4] else [1,4,0,4,4,4,4,4,4,4])) else (if i.val < 4 then [1,3,3,3,4,3,4,4,0,4,4,4,4,4,4,4] else (if i.val < 5 then [0] else [0,1,3,4,3,4,2,3,2,3,3,3,4,0,4,4,4,4,4,4,4])))
theorem basis_action : ∀ i : Fin 6, ∀ p : Fin 8 × ZMod 2,
    frame.symm ((originalWord (basisWords i) : Equiv.Perm (Fin 16)) (frame p))=
      (p.1,p.2+BinaryKernelAxes077.kernelChart.inclusion (Pi.single i 1) p.1) := by decide +kernel

end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
