import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarSurjectivity
import SymmetricSubgroupAsymptotics.SemilinearScalarPairRigidity

/-! Exact scalar coordinates for the actual fixed torus, and its outer
reflection. These are coordinate identities, independent of quotient
automorphisms or root-group reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourTorusScalarCoordinates
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGReeFFourFixedTorusScalarCompatibility CFSGReeFFourFixedTorusScalarSurjectivity
open CFSGReeFFourFixedMiddleTorusAction CFSGReeFFourFixedOuterTorusAction
open CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom

def scalarPair (m : ℕ) (p : (Field m)ˣ×(Field m)ˣ) : (Field m)ˣ×(Field m)ˣ :=
  (outerScalar m p.1 p.2,middleScalar m p.1 p.2)

theorem scalarPair_injective (m : ℕ) : Function.Injective (scalarPair m) :=
  Finite.injective_iff_surjective.mpr (scalar_pair_surjective m)

theorem outer_scalar_formula (m : ℕ) (a b : (Field m)ˣ) :
    outerScalar m a b=a^2*b⁻¹ := by
  unfold outerScalar
  rw [powerHom_apply,Fin.prod_univ_four]
  change a^(2:ℤ)*b^(-1:ℤ)*(alphaUnits m b)^(0:ℤ)*(alphaUnits m a)^(0:ℤ)=a^2*b⁻¹
  simp only [zpow_neg,zpow_ofNat,pow_zero,pow_one,mul_one]

theorem middle_scalar_formula (m : ℕ) (a b : (Field m)ˣ) :
    middleScalar m a b=a⁻¹*b^2*(alphaUnits m b)⁻¹ := by
  unfold middleScalar
  rw [powerHom_apply,Fin.prod_univ_four]
  change a^(-1:ℤ)*b^(2:ℤ)*(alphaUnits m b)^(-1:ℤ)*(alphaUnits m a)^(0:ℤ)=
    a⁻¹*b^2*(alphaUnits m b)⁻¹
  simp only [zpow_neg,zpow_ofNat,pow_zero,pow_one,mul_one]

theorem scalarPair_outer_reflection (m : ℕ) (a b : (Field m)ˣ) :
    scalarPair m (b*a⁻¹,b)=SemilinearScalarPairRigidity.shearReflection (scalarPair m (a,b)) := by
  apply Prod.ext
  · change outerScalar m (b*a⁻¹) b=(outerScalar m a b)⁻¹
    rw [outer_scalar_formula,outer_scalar_formula]
    apply Units.ext
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_pow_eq_pow_val]
    field_simp <;> ring
  · change middleScalar m (b*a⁻¹) b=outerScalar m a b*middleScalar m a b
    rw [middle_scalar_formula,outer_scalar_formula,middle_scalar_formula]
    apply Units.ext
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.val_pow_eq_pow_val]
    field_simp <;> ring

end SymmetricSubgroupAsymptotics.CFSGReeFFourTorusScalarCoordinates
