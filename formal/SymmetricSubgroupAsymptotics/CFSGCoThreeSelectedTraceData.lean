import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Co3
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Literal selected data from the primary's fixed Co3 a*b/e0 diagnostic.
No trajectory action is claimed here. The endpoint and selected nonreturn
coordinates alone are checked; separate sources must prove every actual
pinned matrix-vector transition. No model order or invertibility is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceData

def a : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  CFSG.Models.MatrixData.matrix 2 22 CFSG.Models.MatrixGroups.Co3.rows1

def b : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  CFSG.Models.MatrixData.matrix 2 22 CFSG.Models.MatrixGroups.Co3.rows2

def vectors : Fin 15 → Fin 22 → ZMod 2 := ![
  ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![1,0,1,0,1,1,1,0,1,1,0,1,0,0,1,1,0,1,0,1,1,1],
  ![1,1,1,1,0,1,0,1,1,1,1,0,0,0,0,1,1,0,0,1,1,1],
  ![0,0,0,0,1,1,1,1,1,0,0,0,0,0,1,0,1,0,0,0,1,0],
  ![0,1,0,0,0,0,1,0,1,1,1,1,1,0,1,1,1,1,1,1,1,1],
  ![1,0,0,0,0,0,1,0,0,1,1,1,0,1,1,1,1,0,1,0,0,1],
  ![0,1,0,1,1,0,1,1,0,1,0,1,1,1,1,1,1,0,0,1,1,1],
  ![0,1,1,0,0,1,0,0,1,1,0,1,0,0,1,1,0,0,0,0,0,0],
  ![0,0,1,1,0,0,0,0,0,1,1,1,1,0,0,0,1,1,1,1,0,0],
  ![1,0,0,0,1,1,0,0,0,0,0,0,1,0,1,1,0,1,1,0,0,0],
  ![0,0,1,0,1,0,0,1,0,0,0,1,0,1,0,0,1,1,1,0,1,0],
  ![0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
  ![1,1,1,0,0,1,0,1,0,0,1,1,1,1,1,1,1,1,1,1,0,1],
  ![0,1,0,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0],
  ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]

def afterB : Fin 14 → Fin 22 → ZMod 2 := ![
  ![0,1,1,1,1,1,1,1,1,1,1,1,1,0,1,0,1,0,1,1,0,1],
  ![1,0,0,0,1,0,1,0,0,1,0,0,0,0,1,1,0,0,0,0,1,0],
  ![0,1,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,0,1,0,0,0],
  ![0,1,1,0,0,0,1,0,1,0,1,1,0,0,1,1,0,0,0,1,0,0],
  ![1,0,0,0,0,1,0,0,0,1,0,0,1,0,1,1,1,0,1,1,1,0],
  ![0,1,1,0,0,1,0,0,1,0,0,0,1,1,0,0,1,0,1,0,1,0],
  ![1,1,0,0,0,1,0,0,0,1,0,0,0,1,1,1,0,0,0,0,0,0],
  ![1,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0],
  ![1,1,1,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,1,0],
  ![0,1,1,1,0,1,1,1,1,0,0,0,1,0,1,1,0,1,1,1,1,1],
  ![1,1,0,1,1,1,0,1,1,1,1,0,0,1,0,1,1,1,1,0,1,0],
  ![1,1,1,1,1,1,1,0,1,0,0,1,0,0,0,1,1,1,0,0,1,1],
  ![1,1,0,1,1,0,1,0,1,1,1,0,1,0,1,1,1,0,0,0,1,1],
  ![0,1,0,0,1,0,0,0,1,1,0,0,1,0,1,0,0,0,0,0,0,0]]

theorem initial_eq_e0 : vectors 0 = Pi.single (0 : Fin 22) 1 := by
  funext j
  fin_cases j <;> decide +kernel

theorem final_eq_initial : vectors 14 = vectors 0 := rfl

theorem second_ne_initial : vectors 2 ≠ vectors 0 := by
  intro h
  have hc := congrFun h (1 : Fin 22)
  change (1 : ZMod 2) = 0 at hc
  exact one_ne_zero hc

theorem seventh_ne_initial : vectors 7 ≠ vectors 0 := by
  intro h
  have hc := congrFun h (0 : Fin 22)
  change (0 : ZMod 2) = 1 at hc
  exact zero_ne_one hc

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedTraceData
