import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalBilinearClassGeometry
import SymmetricSubgroupAsymptotics.QuadraticIsometryPolarStabilizer
import Mathlib.Algebra.CharP.Two

/-! In characteristic two the actual split orthogonal quadratic form
has exactly the SAME bilinear polar pairing as the native elementary
symplectic model on the identical paired coordinate index. The equality
retains the actual quadratic form; only its polar group is identified. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPolarCoordinates
open CFSGOrthogonalDIndexBundledQuadratic CFSGSymplecticNaturalBilinearClassGeometry
open QuadraticIsometryPolarStabilizer
variable (K : Type) [Field K] [CharP K 2]

theorem polar_eq_naturalPairing (r : ℕ) :
    (splitQuadraticForm K r).polarBilin = naturalPairing K r := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [splitQuadraticForm_polar, naturalPairing_apply]
  simp only [CFSGOrthogonalDIndexPolarForm.polar,
    CFSGOrthogonalDIndexQuadraticForm.leftPart,
    CFSGOrthogonalDIndexQuadraticForm.rightPart,
    CFSGSymplecticTransvectionGeometry.pairing, dotProduct,
    Function.comp_apply, CharTwo.sub_eq_add, Finset.sum_add_distrib, mul_comm]

theorem polarPreservers_eq (r : ℕ) :
    polarPreservers (splitQuadraticForm K r).polarBilin =
      polarPreservers (naturalPairing K r) :=
  congrArg polarPreservers (polar_eq_naturalPairing K r)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPolarCoordinates
