import SymmetricSubgroupAsymptotics.CFSGQuadraticRootDividedPowers

/-! An actual adjoint-cube equation forces the fourth quadratic
conjugation coefficient to vanish. Cancellation takes place over the
rationals; later integral base change does not divide by a bad prime. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticAdjointCubeConstraint
variable {B : Type*} [Ring B] [Algebra ℚ B]

theorem second_sandwich_zero (e d x : B) (he : e*e=d+d)
    (hed : e*d=0) (hde : d*e=0) (hcube : ⁅e,⁅e,⁅e,x⁆⁆⁆=0) : d*x*d=0 := by
  have hfour : (LieAlgebra.ad ℚ B e^4) x=0 := by
    change ⁅e,⁅e,⁅e,⁅e,x⁆⁆⁆⁆=0
    rw [hcube,lie_zero]
  have hh := CFSGQuadraticRootDividedPowers.ad_pow_eq_factorial_operator e d he hed hde 4 x
  rw [hfour,CFSGIntegralQuadraticRootOperators.operator_four] at hh
  exact (smul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero 4)

end SymmetricSubgroupAsymptotics.CFSGQuadraticAdjointCubeConstraint
