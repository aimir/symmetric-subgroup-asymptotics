import SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieAlgebra
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators
import SymmetricSubgroupAsymptotics.IntegerMatrixLieBaseChange

/-! The SAME quadratic Data integral and field matrix realizations are
actual Lie homomorphisms in every characteristic. No source basis,
faithfulness, good-prime condition or bracket-preservation callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticLieRealization
open CFSG.Models.Chevalley CFSGSerreIntegralLieAlgebra
open CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
  {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem integralRepresentation_map_lie (x y : integralLattice A) :
    integralRepresentation D ⁅x, y⁆ = ⁅integralRepresentation D x, integralRepresentation D y⁆ := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  rw [integralRepresentation_cast]
  change D.rational ⁅x.val, y.val⁆ =
    (Int.castRingHom ℚ).mapMatrix ⁅integralRepresentation D x, integralRepresentation D y⁆
  have hx := integralRepresentation_cast D x
  have hy := integralRepresentation_cast D y
  change (Int.castRingHom ℚ).mapMatrix (integralRepresentation D x) = D.rational x.val at hx
  change (Int.castRingHom ℚ).mapMatrix (integralRepresentation D y) = D.rational y.val at hy
  rw [D.rational.map_lie, IntegerMatrixLieBaseChange.mapMatrix_lie, hx, hy]

def integralLieHom : integralLattice A →ₗ⁅ℤ⁆ Matrix I I ℤ where
  toLinearMap := integralRepresentation D
  map_lie' {x y} := integralRepresentation_map_lie D x y

theorem baseChange_map_lie (K : Type) [Field K] (x y : Space A K) :
    baseChange D K ⁅x, y⁆ = ⁅baseChange D K x, baseChange D K y⁆ :=
  IntegerMatrixLieBaseChange.realization_map_lie (integralLieHom D) K x y

def baseChangeLieHom (K : Type) [Field K] : Space A K →ₗ⁅K⁆ Matrix I I K where
  toLinearMap := baseChange D K
  map_lie' {x y} := baseChange_map_lie D K x y

@[simp] theorem baseChangeLieHom_apply (K : Type) [Field K] (x : Space A K) :
    baseChangeLieHom D K x = baseChange D K x := rfl

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticLieRealization
