import SymmetricSubgroupAsymptotics.CFSGSymplecticBaseChangeOperators
import SymmetricSubgroupAsymptotics.CFSGSquareZeroConjugation

/-! The literal source type-C root operators act on the actual matrix
image by conjugation with the standard square-zero root transvections. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

theorem symplecticBaseChange_rootOperator (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K)
    (x : Space (CartanMatrix.C r).transpose K) :
    symplecticBaseChange K r (rootOperator (CartanMatrix.C r).transpose K neg i t x) =
      (1 + t • rootMatrix K r neg i) * symplecticBaseChange K r x *
        (1 - t • rootMatrix K r neg i) := by
  rw [rootOperator]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    symplecticBaseChange_operator]
  exact CFSGSquareZeroConjugation.operator_sum_eq_conjugation t _ _

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
