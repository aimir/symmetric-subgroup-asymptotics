import SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Polynomial coordinates for the literal sixteen Boolean points.

Evaluation and coefficient extraction are the same subset-incidence map
in characteristic two. Multiplication below is explicitly pointwise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth

abbrev V := Fin 16 → ZMod 2

def monomial (a : Finset (Fin 4)) : V := fun x =>
  if a ⊆ support x then 1 else 0

def evaluate : V →ₗ[ZMod 2] V :=
  Matrix.mulVecLin (fun x a => monomial (support a) x : Matrix (Fin 16) (Fin 16) (ZMod 2))

theorem evaluate_basis (a : Fin 16) :
    evaluate (Pi.single a 1) = monomial (support a) := by
  change Matrix.mulVec (fun x b => monomial (support b) x :
    Matrix (Fin 16) (Fin 16) (ZMod 2)) (Pi.single a 1) = _
  exact Matrix.mulVec_single_one _ a

private theorem evaluate_twice_basis : ∀ a : Fin 16,
    evaluate (evaluate (Pi.single a 1)) = Pi.single a 1 := by decide +kernel

theorem evaluate_involutive : Function.Involutive evaluate := by
  have he : evaluate.comp evaluate = LinearMap.id := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : V) = c • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply, mul_ite]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hs, map_smul,
      evaluate_twice_basis]
  intro v
  exact DFunLike.congr_fun he v

/-- This is a reversible coordinate change on the same point functions. -/
def coordinates : V ≃ₗ[ZMod 2] V where
  toLinearMap := evaluate
  invFun := evaluate
  left_inv := evaluate_involutive
  right_inv := evaluate_involutive

/-- Actual coordinate multiplication is union of monomial supports. -/
theorem monomial_mul (a b : Finset (Fin 4)) :
    monomial a * monomial b = monomial (a ∪ b) := by
  funext x
  by_cases ha : a ⊆ support x <;> by_cases hb : b ⊆ support x <;>
    simp [monomial, ha, hb, Finset.union_subset_iff]

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
