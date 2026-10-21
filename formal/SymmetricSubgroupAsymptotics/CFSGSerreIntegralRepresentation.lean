import SymmetricSubgroupAsymptotics.CFSGSquareZeroDividedPowers
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import Mathlib.Algebra.Module.Submodule.Lattice

/-! A genuine rational Serre representation with square-zero root images
sends the original integral lattice into any actual subring containing its
generator images. This is proved by the original lattice minimality and
integral target divided-power identities, without source injectivity. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSerreIntegralRepresentation
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    {B : Type*} [Ring B] [Algebra ℚ B] (f : RationalLie A →ₗ⁅ℚ⁆ B)

theorem dividedPower_intertwines (negative : Bool) (i : Fin n) (k : ℕ) (x : RationalLie A) :
    f (dividedPower A negative i k x) =
      CFSGSquareZeroDividedPowers.operator (f (rootVector A negative i)) k (f x) := by
  change f ((k.factorial : ℚ)⁻¹ •
      ((LieAlgebra.ad ℚ (RationalLie A) (rootVector A negative i) ^ k) x)) =
    (k.factorial : ℚ)⁻¹ • ((LieAlgebra.ad ℚ B (f (rootVector A negative i)) ^ k) (f x))
  rw [map_smul]
  exact congrArg (fun y : B => (k.factorial : ℚ)⁻¹ • y)
    (lieHom_ad_pow_apply f (rootVector A negative i) x k)

theorem lattice_image_mem_subring (T : Subring B)
    (hgen : ∀ g, f (generator A g) ∈ T)
    (hsquare : ∀ negative i, f (rootVector A negative i) ^ 2 = 0)
    (x : RationalLie A) (hx : x ∈ integralLattice A) : f x ∈ T := by
  let S : Submodule ℤ (RationalLie A) := T.toAddSubgroup.toIntSubmodule.comap
    (f.toLinearMap.restrictScalars ℤ)
  have hcontains : ∀ g, generator A g ∈ S := by
    intro g
    exact hgen g
  have hstable : ∀ negative i k y, y ∈ S → dividedPower A negative i k y ∈ S := by
    intro negative i k y hy
    change f y ∈ T at hy
    change f (dividedPower A negative i k y) ∈ T
    rw [dividedPower_intertwines]
    have he : f (rootVector A negative i) ∈ T := by
      cases negative with
      | false => exact hgen (CartanMatrix.Generators.E i)
      | true => exact hgen (CartanMatrix.Generators.F i)
    have hee : f (rootVector A negative i) * f (rootVector A negative i) = 0 := by
      simpa only [pow_two] using hsquare negative i
    exact CFSGSquareZeroDividedPowers.operator_mem_subring T _ he hee k _ hy
  have hle : integralLattice A ≤ S := sInf_le ⟨hcontains, hstable⟩
  exact hle hx

end SymmetricSubgroupAsymptotics.CFSGSerreIntegralRepresentation
