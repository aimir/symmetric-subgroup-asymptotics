import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketFixedBlocks
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootSupport

/-! The six actual root arrows for the degree-two commutator of the
whole outer parameter and its middle-Weyl conjugate C. Two arrows have
the SAME root and cancel in characteristic two; the other four are
exactly the degree-two roots of the already proved whole blocks D,E.
Their degree-three terms are retained, not equated to one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailBracketRootData
open CFSGIntegerMatrixPairing CFSGReeFFourInnerBracketFixedBlocks
open CFSGE6GeckMiddleRootSupport
local notation "A" => CartanMatrix.E₆

def outerNode : Fin 3→Fin 6 := ![0,5,1]

def arrowLeft : Fin 6→Fin 3 := ![0,1,0,1,2,2]
def arrowRight : Fin 6→Fin 3 := ![1,0,2,2,0,1]

def arrowRoot : Fin 6→CFSGNormTwoRootPairing.Roots A :=
  ![middleRoot 1 2,middleRoot 1 2,
    outerRoot 2 1,outerRoot 2 0,outerRoot 1 1,outerRoot 1 0]

theorem cross_pairing (i j : Fin 3) :
    integerPairing A (Pi.single (outerNode i) (1 : ℤ)) (outerVector 0 j)=
      (![![1,-1,-1],![-1,1,-1],![-1,-1,0]] : Fin 3→Fin 3→ℤ) i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem arrow_sum (i : Fin 6) :
    (Pi.single (outerNode (arrowLeft i)) (1 : ℤ) : Fin 6→ℤ)+
      outerVector 0 (arrowRight i)=(arrowRoot i).val := by
  funext t
  fin_cases i <;> fin_cases t <;> decide +kernel

theorem arrow_height_two (i : Fin 6) : outsideHeight (arrowRoot i).val=2 := by
  fin_cases i <;> decide +kernel

theorem higher_outer_root_height (b : Fin 2) :
    outsideHeight (outerRoot b.succ 2).val=3 := by
  fin_cases b <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTailBracketRootData
