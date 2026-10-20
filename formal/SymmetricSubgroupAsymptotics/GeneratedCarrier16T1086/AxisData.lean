import SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.AxisElementLiterals000

/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryChart16T1086

def axisElement (i : Fin 4) : Equiv.Perm (Fin 16) :=
  (if i.val < 2 then (if i.val < 1 then axisElementLiteral0 else axisElementLiteral1) else (if i.val < 3 then axisElementLiteral2 else axisElementLiteral3))

def axisGenerators (j : Fin 2) := axisElement (#[1,2][j.val]!)
def axisNextTable (i : Fin 4) : Array (Fin 4) :=
  (if i.val < 2 then (if i.val < 1 then #[1,2] else #[0,3]) else (if i.val < 3 then #[3,0] else #[2,1]))
def axisWordTable (i : Fin 4) : List (Fin 2) :=
  (if i.val < 2 then (if i.val < 1 then [] else [0]) else (if i.val < 3 then [1] else [0,1]))

end SymmetricSubgroupAsymptotics.BinaryChart16T1086
