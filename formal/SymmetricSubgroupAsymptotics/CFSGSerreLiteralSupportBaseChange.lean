import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSupport

/-! Literal rational support of the SAME original source element passes
through its actual integer-matrix realization to every coefficient ring.
Only entrywise integer zeros are transported, never rational eigenvalue
separation after reduction. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreLiteralSupportBaseChange
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix CFSGGradedMatrixSupport
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I W : Type*} [Fintype I] [DecidableEq I]

/-- The actual integral representation has the exact rational entry
support. Rational support is proved separately from the native/old root
relations, not supplied at the final classifier boundary. -/
theorem integral_support (D : Data A I) (weight : I → W) (f : W → W)
    (x : integralLattice A) (h : Supported weight f (D.rational x.val)) :
    Supported weight f (integralRepresentation D x) := by
  intro i j hij
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  have he := congrArg (fun M : Matrix I I ℚ => M i j)
    (integralRepresentation_cast D x)
  change (integralRepresentation D x i j : ℚ) = D.rational x.val i j at he
  rw [he, h i j hij, Int.cast_zero]

/-- No characteristic restriction is needed to preserve literal zeros. -/
theorem baseChange_tmul_support (D : Data A I) (weight : I → W) (f : W → W)
    (x : integralLattice A) (h : Supported weight f (D.rational x.val))
    (K : Type*) [CommRing K] (a : K) :
    Supported weight f (baseChange D K (a ⊗ₜ[ℤ] x)) := by
  rw [baseChange_tmul]
  intro i j hij
  change a * (integralRepresentation D x i j : K) = 0
  rw [integral_support D weight f x h i j hij, Int.cast_zero, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGSerreLiteralSupportBaseChange
