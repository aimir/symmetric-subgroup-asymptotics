import SymmetricSubgroupAsymptotics.CFSGAlternatingPairComposition
import SymmetricSubgroupAsymptotics.CFSGAlternatingPairSums
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic.Abel

/-! Two actual group elements with shared-vector pair displacements
multiply to the actual element with their summed pair displacement,
when the indicated cross composition vanishes. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearPairActionProduct
open CFSGAlternatingPairOperator
variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

theorem mul_eq_of_pair_actions (rho : G →* (V ≃ₗ[K] V)) (hrho : Function.Injective rho)
    (B : LinearMap.BilinForm K V) (u v w : V) (x y z : G)
    (hx : ∀ t, rho x t = t + pairOperator B u v t)
    (hy : ∀ t, rho y t = t + pairOperator B u w t)
    (hz : ∀ t, rho z t = t + pairOperator B u (v + w) t)
    (hcomp : (pairOperator B u v).comp (pairOperator B u w) = 0) : x * y = z := by
  apply hrho
  apply LinearEquiv.ext
  intro t
  rw [map_mul]
  change rho x (rho y t) = rho z t
  rw [hy, hx, hz, pairOperator_add_right, LinearMap.add_apply, map_add]
  have hzero := LinearMap.congr_fun hcomp t
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
  rw [hzero]
  abel

end SymmetricSubgroupAsymptotics.CFSGLinearPairActionProduct
