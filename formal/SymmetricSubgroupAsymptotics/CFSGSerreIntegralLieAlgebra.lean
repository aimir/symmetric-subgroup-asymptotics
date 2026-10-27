import SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieClosure
import Mathlib.Algebra.Lie.BaseChange

/-! Genuine Lie structures on the literal integral lattice and its original
tensor-product space. These are available in every characteristic. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieAlgebra
open CFSG.Models.Chevalley CFSGSerreIntegralLieClosure
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

instance integralLieRing : LieRing (integralLattice A) :=
  inferInstanceAs (LieRing (integralLieSubalgebra A))

instance integralLieAlgebra : LieAlgebra ℤ (integralLattice A) :=
  inferInstanceAs (LieAlgebra ℤ (integralLieSubalgebra A))

@[simp] theorem integralBracket_val (x y : integralLattice A) :
    (⁅x,y⁆ : integralLattice A).val = ⁅x.val,y.val⁆ := rfl

def integralInclusion : integralLattice A →ₗ⁅ℤ⁆ RationalLie A where
  toLinearMap := (integralLattice A).subtype
  map_lie' := rfl

theorem integralInclusion_injective : Function.Injective (integralInclusion A) :=
  Subtype.val_injective

variable (K : Type) [Field K]

theorem spaceBracket_tmul (a b : K) (x y : integralLattice A) :
    (⁅a ⊗ₜ[ℤ] x, b ⊗ₜ[ℤ] y⁆ : Space A K) = (a*b) ⊗ₜ[ℤ] ⁅x,y⁆ :=
  LieAlgebra.ExtendScalars.bracket_tmul ℤ K (integralLattice A)
    (integralLattice A) a b x y

end SymmetricSubgroupAsymptotics.CFSGSerreIntegralLieAlgebra
