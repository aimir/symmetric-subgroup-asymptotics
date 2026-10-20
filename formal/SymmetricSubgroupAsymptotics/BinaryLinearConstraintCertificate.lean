import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi

/-! Sparse row identities imply the corresponding binary linear
constraints. The rows are actual coefficient vectors, and the retained
sum identities are checked in Lean; a producer's reported matrix rank
or solvability flag is never used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Each target row is a displayed sum of actual input rows. All binary
cancellation remains part of the checked identity. -/
structure BinaryLinearConstraintCertificate
    {w a b : ℕ}
    (input : Fin a → Fin w → ZMod 2)
    (target : Fin b → Fin w → ZMod 2) where
  support : Fin b → Finset (Fin a)
  target_eq : ∀ j, target j = ∑ i ∈ support j, input i

namespace BinaryLinearConstraintCertificate

variable {w a b : ℕ}
  {input : Fin a → Fin w → ZMod 2}
  {target : Fin b → Fin w → ZMod 2}
  (C : BinaryLinearConstraintCertificate input target)

include C

/-- The finite row witness proves the implication on every binary
assignment, without enumerating those assignments. -/
theorem target_dotProduct_eq_zero
    (x : Fin w → ZMod 2)
    (hx : ∀ i, dotProduct (input i) x = 0) (j : Fin b) :
    dotProduct (target j) x = 0 := by
  rw [C.target_eq j]
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun i _ => hx i

/-- Simultaneous annihilation of the literal input rows implies
simultaneous annihilation of the literal target rows. -/
theorem target_vanishes
    (x : Fin w → ZMod 2)
    (hx : ∀ i, dotProduct (input i) x = 0) :
    ∀ j, dotProduct (target j) x = 0 :=
  C.target_dotProduct_eq_zero x hx

end BinaryLinearConstraintCertificate

/-- Dot product as a literal binary linear functional. -/
def binaryRowFunctional {w : ℕ} (row : Fin w → ZMod 2) :
    (Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := dotProduct row
  map_add' := dotProduct_add row
  map_smul' := fun a x => dotProduct_smul a row x

/-- Equality of binary linear functionals is checked on the actual
coordinate basis, rather than on all binary assignments. -/
theorem binaryLinearFunctional_ext_basis {w : ℕ}
    {f g : (Fin w → ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearMap.pi_ext
  intro i a
  have hs : Pi.single i a = a • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  rw [hs, map_smul, map_smul, h i]

end SymmetricSubgroupAsymptotics
