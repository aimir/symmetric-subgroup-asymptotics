import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleWeylMatrix
import SymmetricSubgroupAsymptotics.MatrixBinaryAffineFactor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! ONE selected flat matrix-product coefficient certificate and ONE
symbolic affine vector step. No global ordered-chart claim is made. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMatrixPolynomialPilot
open CFSGReeFFourBinarySeedOuterMatrix MatrixBinaryAffineFactor

private def productRows : Fin 26 → Finset (Fin 26) :=
  ![{0,10},
    {1},
    {2},
    {6},
    {5},
    {4},
    {2,3},
    {10},
    {9},
    {6,8},
    {5,7},
    {6,11},
    {17},
    {15},
    {19},
    {9,13},
    {17,18},
    {6,8,11,12},
    {15,16},
    {1,10,14},
    {17,20},
    {24},
    {23},
    {19,22},
    {17,18,20,21},
    {24,25} ]

def flatProduct : Matrix (Fin 26) (Fin 26) (ZMod 2) := fun i j =>
  if j∈productRows i then 1 else 0

theorem flat_product_entry : ∀i j : Fin 26,
    flatProduct i j=(CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*outerMatrix) i j := by
  decide +kernel

theorem flat_product_eq : flatProduct=
    CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix*outerMatrix := by
  funext i j
  exact flat_product_entry i j

def firstState (b : ZMod 2) : Fin 26 → ZMod 2 :=
  ![0,0,0,0,0,0,0,1,b,0,b,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 ]

theorem first_affine_stage (b : ZMod 2) :
    (affineFactor b CFSGReeFFourBinarySeedMiddleMatrix.matrix).mulVec
      (Pi.single 7 1)=firstState b := by
  rw [affineFactor_mulVec,Matrix.mulVec_single_one]
  funext j
  fin_cases j <;>
    simp [firstState,CFSGReeFFourBinarySeedMiddleMatrix.matrix,
      CFSGReeFFourBinarySeedMiddleMatrix.rows,Matrix.col_apply,Pi.single_apply,
      Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> ring

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMatrixPolynomialPilot
