import SymmetricSubgroupAsymptotics.BinaryQuadraticField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The literal clock, shift, Fourier and phase matrices on F4^3.
All certificates concern these four displayed matrices only. In
characteristic two, 3=1, so the Fourier matrix needs no scalar square-root
normalization. This does not assume an order or recognition of GU3(2). -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.QuaternaryPauliMatrices
open BinaryQuadraticField
abbrev K := Scalar
abbrev Mat := Matrix (Fin 3) (Fin 3) K

def shiftMatrix : Mat := !![0,0,1;1,0,0;0,1,0]
def shiftInverse : Mat := !![0,1,0;0,0,1;1,0,0]
def clockMatrix : Mat := !![1,0,0;0,omega,0;0,0,omega^2]
def clockInverse : Mat := !![1,0,0;0,omega^2,0;0,0,omega]
def fourierMatrix : Mat := !![1,1,1;1,omega,omega^2;1,omega^2,omega]
def fourierInverse : Mat := !![1,1,1;1,omega^2,omega;1,omega,omega^2]
def phaseMatrix : Mat := !![1,0,0;0,1,0;0,0,omega]
def phaseInverse : Mat := !![1,0,0;0,1,0;0,0,omega^2]

def adjoint (A : Mat) : Mat := A.transpose.map (fun z => z^2)

theorem omega_cube : omega^3=(1:K) := by decide +kernel
theorem omega_ne_one : omega≠(1:K) := by decide +kernel

theorem shift_inverse : shiftMatrix*shiftInverse=1 ∧ shiftInverse*shiftMatrix=1 := by
  decide +kernel

theorem clock_inverse : clockMatrix*clockInverse=1 ∧ clockInverse*clockMatrix=1 := by
  decide +kernel

theorem fourier_inverse : fourierMatrix*fourierInverse=1 ∧ fourierInverse*fourierMatrix=1 := by
  decide +kernel

theorem phase_inverse : phaseMatrix*phaseInverse=1 ∧ phaseInverse*phaseMatrix=1 := by
  decide +kernel

/-- Each displayed matrix preserves the standard F4 Hermitian form. -/
theorem unitary_matrices :
    adjoint shiftMatrix*shiftMatrix=1 ∧ adjoint clockMatrix*clockMatrix=1 ∧
    adjoint fourierMatrix*fourierMatrix=1 ∧ adjoint phaseMatrix*phaseMatrix=1 := by
  decide +kernel

theorem pauli_relations : shiftMatrix^3=1 ∧ clockMatrix^3=1 ∧
    clockMatrix*shiftMatrix=(omega • (shiftMatrix*clockMatrix)) := by
  decide +kernel

theorem fourier_normalizes :
    fourierMatrix*shiftMatrix*fourierInverse=clockMatrix ∧
    fourierMatrix*clockMatrix*fourierInverse=shiftInverse := by
  decide +kernel

theorem phase_normalizes :
    phaseMatrix*shiftMatrix*phaseInverse=shiftMatrix*clockMatrix ∧
    phaseMatrix*clockMatrix*phaseInverse=clockMatrix := by
  decide +kernel

def shift : Matˣ := ⟨shiftMatrix,shiftInverse,shift_inverse.1,shift_inverse.2⟩
def clock : Matˣ := ⟨clockMatrix,clockInverse,clock_inverse.1,clock_inverse.2⟩
def fourier : Matˣ := ⟨fourierMatrix,fourierInverse,fourier_inverse.1,fourier_inverse.2⟩
def phase : Matˣ := ⟨phaseMatrix,phaseInverse,phase_inverse.1,phase_inverse.2⟩

end SymmetricSubgroupAsymptotics.QuaternaryPauliMatrices
