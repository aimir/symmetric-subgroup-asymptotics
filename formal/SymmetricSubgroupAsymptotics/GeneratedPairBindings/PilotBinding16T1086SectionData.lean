import SymmetricSubgroupAsymptotics.GeneratedPairBindings.PilotBinding16T1086SourceMap

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
local instance pilotSectionDataGroup : Group SourceTop := BinaryTopSource056.group

def sectionWords (q : SourceTop) : List (Fin 4) := (if q.index.val < 8 then (if q.index.val < 4 then (if q.index.val < 2 then (if q.index.val < 1 then [2,3,3,3] else [3]) else (if q.index.val < 3 then [2,3,2,3,3] else [3,2])) else (if q.index.val < 6 then (if q.index.val < 5 then [2,3,2] else [3,2,3,3]) else (if q.index.val < 7 then [2,3] else [3,3,3]))) else (if q.index.val < 12 then (if q.index.val < 10 then (if q.index.val < 9 then [2] else [2,3,2,3]) else (if q.index.val < 11 then [2,3,2,3,3,3] else [2,3,3])) else (if q.index.val < 14 then (if q.index.val < 13 then [3,3] else [3,2,3,3,3]) else (if q.index.val < 15 then [3,2,3] else []))))
def sectionMap (q : SourceTop) : Original := originalWord (sectionWords q)
end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1086
