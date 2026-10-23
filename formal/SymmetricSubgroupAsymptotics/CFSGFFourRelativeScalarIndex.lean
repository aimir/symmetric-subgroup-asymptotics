import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom
import Mathlib.Data.Matrix.Cartan

/-! The actual four relative coroot exponents have determinant one.
An explicit integral right inverse proves the monomial map is surjective
over EVERY commutative group, including unit groups in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex
open CFSGIntegerMatrixPowerHom

/-- Root-coordinate rows and torus-coordinate columns give the transpose
of Mathlib's literal F4 Cartan matrix. -/
def relativeCartan : Matrix (Fin 4) (Fin 4) ℤ := CartanMatrix.F₄.transpose

def inverseExponents : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2,3,2,1;
     3,6,4,2;
     4,8,6,3;
     2,4,3,2]

theorem relativeCartan_right_inverse : relativeCartan*inverseExponents=1 := by decide

theorem powerHom_surjective {G : Type*} [CommGroup G] :
    Function.Surjective (powerHom (G := G) relativeCartan) := by
  intro x
  exact ⟨powerHom inverseExponents x,
    powerHom_rightInverse relativeCartan inverseExponents relativeCartan_right_inverse x⟩

theorem range_index_eq_one {G : Type*} [CommGroup G] :
    (powerHom (G := G) relativeCartan).range.index=1 := by
  rw [MonoidHom.range_eq_top.mpr powerHom_surjective,Subgroup.index_top]

end SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex
