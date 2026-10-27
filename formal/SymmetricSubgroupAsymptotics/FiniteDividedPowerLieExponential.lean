import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! A length-four divided-power system with the Leibniz identities defines
Lie endomorphisms in every characteristic. The degree4,5,6 identities pay
for all cross terms; it is not legitimate to discard them individually. -/
set_option autoImplicit false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteDividedPowerLieExponential
variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

def exponential (F : ℕ → Module.End K L) (t : K) : Module.End K L :=
  ∑ j ∈ Finset.range 4, t^j • F j

theorem map_lie (F : ℕ → Module.End K L) (hzero : F 0 = LinearMap.id)
    (hge : ∀ k, 4 ≤ k → F k = 0)
    (hleib : ∀ k x y, F k ⁅x,y⁆ =
      ∑ j ∈ Finset.range (k+1), ⁅F j x, F (k-j) y⁆)
    (t : K) (x y : L) :
    exponential F t ⁅x,y⁆ = ⁅exponential F t x, exponential F t y⁆ := by
  have h1 := hleib 1 x y
  have h2 := hleib 2 x y
  have h3 := hleib 3 x y
  have h4 := hleib 4 x y
  have h5 := hleib 5 x y
  have h6 := hleib 6 x y
  simp [Finset.sum_range_succ, hzero, hge 4 (by decide),
    hge 5 (by decide), hge 6 (by decide)] at h1 h2 h3 h4 h5 h6
  simp only [exponential, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add, LinearMap.add_apply, LinearMap.smul_apply,
    hzero, LinearMap.id_apply, pow_zero, one_smul, pow_one,
    add_lie, lie_add, smul_lie, lie_smul]
  rw [h1, h2, h3]
  linear_combination (norm := module) t^4 • h4 + t^5 • h5 + t^6 • h6

end SymmetricSubgroupAsymptotics.FiniteDividedPowerLieExponential
