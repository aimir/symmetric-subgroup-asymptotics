import SymmetricSubgroupAsymptotics.CFSGSymplecticBaseChange
import SymmetricSubgroupAsymptotics.CFSGSymplecticIntegralOperators

/-! Every actual base-changed source divided power intertwines with its
integral matrix formula. This uses the original integral lattice and
tensor product, including in characteristics two and three. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

theorem symplecticBaseChange_operator (K : Type*) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) (k : ℕ)
    (x : K ⊗[ℤ] integralLattice (CartanMatrix.C r).transpose) :
    symplecticBaseChange K r
      ((integralOperator (CartanMatrix.C r).transpose neg i k).baseChange K x) =
      CFSGIntegralSquareZeroOperators.operator K (rootMatrix K r neg i) k
        (symplecticBaseChange K r x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, symplecticBaseChange_tmul,
      integralRepresentation_operator, symplecticBaseChange_tmul]
    change a • (Int.castRingHom K).mapMatrix
      (CFSGIntegralSquareZeroOperators.operator ℤ (rootMatrix ℤ r neg i) k
        (integralSymplecticRepresentation r x)) =
      CFSGIntegralSquareZeroOperators.operator K (rootMatrix K r neg i) k
        (a • (Int.castRingHom K).mapMatrix (integralSymplecticRepresentation r x))
    rw [CFSGIntegralSquareZeroOperators.map_operator, map_rootMatrix,
      CFSGIntegralSquareZeroOperators.operator_changeScalars ℤ K, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
