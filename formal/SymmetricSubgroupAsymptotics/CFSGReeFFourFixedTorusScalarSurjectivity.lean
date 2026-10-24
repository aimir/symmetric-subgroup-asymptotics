import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedMiddleTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterTorusAction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Both positive relative scalars are realized simultaneously by an
actual fixed torus word. The explicit inverse uses alpha squared equal
to squaring; no norm surjectivity or root extraction is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarSurjectivity
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGReeFFourFixedTorusScalarCompatibility
open CFSGReeFFourFixedMiddleTorusAction CFSGReeFFourFixedOuterTorusAction
open CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom

def inverseFirst (m : ℕ) (r s : (Field m)ˣ) : (Field m)ˣ :=
  r^2*alphaUnits m r*s^3*(alphaUnits m s)^2

def inverseSecond (m : ℕ) (r s : (Field m)ˣ) : (Field m)ˣ :=
  r^3*(alphaUnits m r)^2*s^6*(alphaUnits m s)^4

private theorem outer_scalar_formula (m : ℕ) (a b : (Field m)ˣ) :
    outerScalar m a b=a^2*b⁻¹ := by
  unfold outerScalar
  rw [powerHom_apply,Fin.prod_univ_four]
  change a^(2:ℤ)*b^(-1:ℤ)*(alphaUnits m b)^(0:ℤ)*(alphaUnits m a)^(0:ℤ)=a^2*b⁻¹
  simp only [zpow_neg,zpow_ofNat,pow_zero,pow_one,mul_one]

private theorem middle_scalar_formula (m : ℕ) (a b : (Field m)ˣ) :
    middleScalar m a b=a⁻¹*b^2*(alphaUnits m b)⁻¹ := by
  unfold middleScalar
  rw [powerHom_apply,Fin.prod_univ_four]
  change a^(-1:ℤ)*b^(2:ℤ)*(alphaUnits m b)^(-1:ℤ)*(alphaUnits m a)^(0:ℤ)=
    a⁻¹*b^2*(alphaUnits m b)⁻¹
  simp only [zpow_neg,zpow_ofNat,pow_zero,pow_one,mul_one]

theorem outer_scalar_inverse (m : ℕ) (r s : (Field m)ˣ) :
    outerScalar m (inverseFirst m r s) (inverseSecond m r s)=r := by
  rw [outer_scalar_formula]
  apply Units.ext
  simp only [inverseFirst,inverseSecond,Units.val_mul,Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp <;> ring

theorem middle_scalar_inverse (m : ℕ) (r s : (Field m)ˣ) :
    middleScalar m (inverseFirst m r s) (inverseSecond m r s)=s := by
  rw [middle_scalar_formula]
  simp only [inverseFirst,inverseSecond,map_mul,map_pow,alphaUnits_twice]
  apply Units.ext
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val]
  field_simp <;> ring

theorem scalar_pair_surjective (m : ℕ) :
    Function.Surjective (fun p : (Field m)ˣ×(Field m)ˣ=>
      (outerScalar m p.1 p.2,middleScalar m p.1 p.2)) := by
  rintro ⟨r,s⟩
  exact ⟨(inverseFirst m r s,inverseSecond m r s),
    Prod.ext (outer_scalar_inverse m r s) (middle_scalar_inverse m r s)⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarSurjectivity
