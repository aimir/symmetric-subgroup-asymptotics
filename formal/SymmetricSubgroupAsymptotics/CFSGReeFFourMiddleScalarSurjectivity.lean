import SymmetricSubgroupAsymptotics.CFSGReeFFourTorusScalarCoordinates

/-! The middle scalar on the actual one-dimensional torus slice is
bijective. Its inverse uses the literal lower Frobenius map, so this
does not need a whole rank-one identification or an automorphism lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleScalarSurjectivity
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorusScalarCompatibility
open CFSGReeFFourFixedMiddleTorusAction CFSGReeFFourTorusScalarCoordinates

def scalarInverse (m : ℕ) (r : (Field m)ˣ) : (Field m)ˣ :=
  r * Units.map (beta m).toMonoidHom r

theorem middleScalar_inverse (m : ℕ) (r : (Field m)ˣ) :
    middleScalar m 1 (scalarInverse m r) = r := by
  have hb : alphaUnits m (Units.map (beta m).toMonoidHom r) = r := by
    apply Units.ext
    exact alpha_beta m r
  have hs : (Units.map (beta m).toMonoidHom r) ^ 2 = alphaUnits m r := by
    apply Units.ext
    exact (alpha_eq_beta_square m r).symm
  rw [middle_scalar_formula, scalarInverse, map_mul, hb, mul_pow, hs]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    inv_one, one_mul]
  field_simp <;> ring

theorem middleScalar_surjective (m : ℕ) :
    Function.Surjective (fun b : (Field m)ˣ => middleScalar m 1 b) :=
  fun r => ⟨scalarInverse m r, middleScalar_inverse m r⟩

theorem middleScalar_injective (m : ℕ) :
    Function.Injective (fun b : (Field m)ˣ => middleScalar m 1 b) :=
  Finite.injective_iff_surjective.mpr (middleScalar_surjective m)

def middleScalarEquiv (m : ℕ) : (Field m)ˣ ≃ (Field m)ˣ where
  toFun b := middleScalar m 1 b
  invFun := scalarInverse m
  left_inv b := (middleScalar_injective m) (middleScalar_inverse m (middleScalar m 1 b))
  right_inv := middleScalar_inverse m

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleScalarSurjectivity
