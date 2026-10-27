import SymmetricSubgroupAsymptotics.CFSGSerreIntegralDividedPowerLie
import SymmetricSubgroupAsymptotics.FiniteDividedPowerLieExponential

/-! Root polynomials preserve the genuine bracket on the original tensor
space whenever their actual integral operators vanish from degree4.
The nilpotence premise is explicit and must be proved in each root type. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreRootLieHom
open CFSG.Models.Chevalley CFSGSerreDividedPowers
open CFSGSerreIntegralLieAlgebra CFSGSerreIntegralDividedPowerLie
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

theorem rootOperator_map_lie (negative : Bool) (i : Fin r)
    (hge : ∀ k, 4 ≤ k → integralOperator A negative i k = 0)
    (t : K) (x y : Space A K) :
    rootOperator A K negative i t ⁅x,y⁆ =
      ⁅rootOperator A K negative i t x,rootOperator A K negative i t y⁆ := by
  apply FiniteDividedPowerLieExponential.map_lie
    (fun k => (integralOperator A negative i k).baseChange K)
  · rw [integralOperator_zero]
    change (LinearMap.id : integralLattice A →ₗ[ℤ] integralLattice A).baseChange K = _
    exact LinearMap.baseChange_id
  · intro k hk
    rw [hge k hk, LinearMap.baseChange_zero]
  · intro k u v
    exact baseChangeIntegralOperator_lie A K negative i k u v

def rootLieHom (negative : Bool) (i : Fin r)
    (hge : ∀ k, 4 ≤ k → integralOperator A negative i k = 0)
    (t : K) : Space A K →ₗ⁅K⁆ Space A K where
  toLinearMap := rootOperator A K negative i t
  map_lie' := fun {x y} => rootOperator_map_lie A K negative i hge t x y

end SymmetricSubgroupAsymptotics.CFSGSerreRootLieHom
