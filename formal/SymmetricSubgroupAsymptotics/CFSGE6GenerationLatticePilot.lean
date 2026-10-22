import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases

/-! One selected E6 Coxeter/torus pilot, on six original integral
coordinates. These are coefficient identities, not group-generation claims. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationLatticePilot
open CFSGIntegerMatrixPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSignedCartanReflections
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinateLatticeWord
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

def coxeterWord : List (Fin 6) := [0,1,2,3,4,5]
def coxeterMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0,1,0,0,0,-1;
     0,0,1,0,0,-1;
     1,1,0,0,0,-1;
     0,1,1,0,0,-1;
     0,0,0,1,0,-1;
     0,0,0,0,1,-1]

def inverseZero : Fin 6→ℤ := ![-1,0,-1,-1,-1,-1]
def torusFunctional : (Fin 6→ℤ)→ₗ[ℤ]ℤ :=
  integerPairing CartanMatrix.E₆ ((Pi.single 4 1 : Fin 6→ℤ)+Pi.single 5 1)

theorem coxeter_lattice_matrix : latticeWord CartanMatrix.E₆ coxeterWord=coxeterMatrix := by decide

theorem coxeter_preimage_zero : coxeterMatrix*ᵥinverseZero=Pi.single 0 1 := by decide

theorem coxeter_preimage_five : coxeterMatrix*ᵥ(Pi.single 4 1 : Fin 6→ℤ)=Pi.single 5 1 := by decide

theorem functional_zero : torusFunctional (Pi.single 0 1)=0 := by decide
theorem functional_four : torusFunctional (Pi.single 4 1)=1 := by decide
theorem functional_five : torusFunctional (Pi.single 5 1)=1 := by decide
theorem functional_inverseZero : torusFunctional inverseZero= -1 := by decide

def coxeterLinear : (Fin 6→ℤ)≃ₗ[ℤ](Fin 6→ℤ) :=
  wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index coxeterWord

theorem coxeter_linear_matrix : coxeterMatrix.mulVecLin=coxeterLinear.toLinearMap := by
  rw [←coxeter_lattice_matrix]
  exact latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos coxeterWord

theorem inverse_simple_zero : coxeterLinear.symm (Pi.single 0 1)=inverseZero := by
  have he := LinearMap.congr_fun coxeter_linear_matrix inverseZero
  change coxeterMatrix*ᵥinverseZero=coxeterLinear inverseZero at he
  rw [coxeter_preimage_zero] at he
  exact (congrArg coxeterLinear.symm he).trans (coxeterLinear.symm_apply_apply inverseZero)

theorem inverse_simple_five : coxeterLinear.symm (Pi.single 5 1)=Pi.single 4 1 := by
  have he := LinearMap.congr_fun coxeter_linear_matrix (Pi.single 4 (1:ℤ))
  change coxeterMatrix*ᵥ(Pi.single 4 1 : Fin 6→ℤ)=coxeterLinear (Pi.single 4 1) at he
  rw [coxeter_preimage_five] at he
  exact (congrArg coxeterLinear.symm he).trans (coxeterLinear.symm_apply_apply (Pi.single 4 1))

theorem pullback_zero : torusFunctional (coxeterLinear.symm (Pi.single 0 1))= -1 := by
  rw [inverse_simple_zero,functional_inverseZero]

theorem pullback_five : torusFunctional (coxeterLinear.symm (Pi.single 5 1))=1 := by
  rw [inverse_simple_five,functional_four]

end SymmetricSubgroupAsymptotics.CFSGE6GenerationLatticePilot
