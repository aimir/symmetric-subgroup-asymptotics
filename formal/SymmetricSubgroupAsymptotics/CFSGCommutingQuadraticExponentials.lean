import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! Rational exponential collecting for a commuting cubic-nilpotent
pair. The sum-cube identity removes the degree-three and degree-four
cross coefficients explicitly. Application to a noncommutative matrix
algebra requires passing to the commutative subalgebra of the actual
commuting pair; no matrix algebra is assumed commutative. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCommutingQuadraticExponentials
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def exponential (a : ℚ) (x : R) : R := 1+a • x+(a^2/2) • x^2

theorem product_difference (x y : R) (hx : x^3=0) (hy : y^3=0)
    (hsum : (x+y)^3=0) (a : ℚ) :
    exponential a (x+y)*exponential a (-x)=exponential a y := by
  have hexp : (x+y)^3=x^3+y^3+(3:ℚ) • (x^2*y+x*y^2) := by
    simp only [Algebra.smul_def,map_ofNat]
    ring
  simp only [hx,hy,hsum,zero_add] at hexp
  have hmixed : x^2*y+x*y^2=0 := by
    have hh := congrArg (fun z : R=>(1/3:ℚ) • z) hexp.symm
    simpa only [smul_smul,show (1/3:ℚ)*3=1 by norm_num,one_smul,smul_zero] using hh
  have hfour : x^2*y^2=0 := by
    linear_combination x*hmixed-y*hx
  let ar : R := algebraMap ℚ R a
  let br : R := algebraMap ℚ R (a^2/2)
  have htwo : (2:R)*br=ar^2 := by
    have hh := congrArg (algebraMap ℚ R) (show (2:ℚ)*(a^2/2)=a^2 by ring)
    simpa only [map_mul,map_ofNat,map_pow] using hh
  simp only [exponential,Algebra.smul_def]
  change (1+ar*(x+y)+br*(x+y)^2)*(1+ar*(-x)+br*(-x)^2)=1+ar*y+br*y^2
  linear_combination (x^2+x*y)*htwo-ar*br*hmixed+br^2*hfour+br^2*(x+2*y)*hx

end SymmetricSubgroupAsymptotics.CFSGCommutingQuadraticExponentials
