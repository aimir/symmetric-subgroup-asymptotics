import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreIntegralRepresentation
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The concrete rational type-C representation sends the original
integral Serre lattice to literal integer matrices. It therefore restricts
to a genuine integer-linear representation, without source faithfulness. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

def integerMatrices (r : ℕ) : Subring (Mat ℚ r) := (Int.castRingHom ℚ).mapMatrix.range

theorem rationalSymplecticRepresentation_lattice_integral (r : ℕ)
    (x : RationalLie (CartanMatrix.C r).transpose)
    (hx : x ∈ integralLattice (CartanMatrix.C r).transpose) :
    rationalSymplecticRepresentation r x ∈ integerMatrices r := by
  apply CFSGSerreIntegralRepresentation.lattice_image_mem_subring
    (CartanMatrix.C r).transpose (rationalSymplecticRepresentation r) (integerMatrices r)
    ?_ ?_ x hx
  · intro g
    cases g with
    | H i =>
      rw [rationalSymplecticRepresentation_H]
      exact ⟨cartan ℤ r i, map_cartan (Int.castRingHom ℚ) r i⟩
    | E i =>
      rw [rationalSymplecticRepresentation_E]
      exact ⟨positive ℤ r i, map_positive (Int.castRingHom ℚ) r i⟩
    | F i =>
      rw [rationalSymplecticRepresentation_F]
      exact ⟨negative ℤ r i, map_negative (Int.castRingHom ℚ) r i⟩
  · intro negativeRoot i
    cases negativeRoot with
    | false =>
      change rationalSymplecticRepresentation r
        (generator (CartanMatrix.C r).transpose (CartanMatrix.Generators.E i)) ^ 2 = 0
      rw [rationalSymplecticRepresentation_E]
      exact positive_sq_zero ℚ r i
    | true =>
      change rationalSymplecticRepresentation r
        (generator (CartanMatrix.C r).transpose (CartanMatrix.Generators.F i)) ^ 2 = 0
      rw [rationalSymplecticRepresentation_F]
      exact negative_sq_zero ℚ r i

def intMatrixLinearMap (r : ℕ) : Mat ℤ r →ₗ[ℤ] Mat ℚ r :=
  (Int.castRingHom ℚ).mapMatrix.toAddMonoidHom.toIntLinearMap

theorem intMatrixLinearMap_injective (r : ℕ) : Function.Injective (intMatrixLinearMap r) := by
  intro X Y h
  apply Matrix.ext
  intro i j
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  exact congrArg (fun Z : Mat ℚ r => Z i j) h

def latticeRationalMap (r : ℕ) :
    integralLattice (CartanMatrix.C r).transpose →ₗ[ℤ] Mat ℚ r :=
  ((rationalSymplecticRepresentation r).toLinearMap.restrictScalars ℤ).domRestrict
    (integralLattice (CartanMatrix.C r).transpose)

def latticeMapToIntegerRange (r : ℕ) :
    integralLattice (CartanMatrix.C r).transpose →ₗ[ℤ] (intMatrixLinearMap r).range :=
  (latticeRationalMap r).codRestrict (intMatrixLinearMap r).range (fun x =>
    rationalSymplecticRepresentation_lattice_integral r x.val x.property)

def integralSymplecticRepresentation (r : ℕ) :
    integralLattice (CartanMatrix.C r).transpose →ₗ[ℤ] Mat ℤ r :=
  (LinearEquiv.ofInjective (intMatrixLinearMap r) (intMatrixLinearMap_injective r)).symm.toLinearMap.comp
    (latticeMapToIntegerRange r)

theorem integralSymplecticRepresentation_cast (r : ℕ)
    (x : integralLattice (CartanMatrix.C r).transpose) :
    intMatrixLinearMap r (integralSymplecticRepresentation r x) =
      rationalSymplecticRepresentation r x.val := by
  have h := (LinearEquiv.ofInjective (intMatrixLinearMap r)
    (intMatrixLinearMap_injective r)).apply_symm_apply (latticeMapToIntegerRange r x)
  exact congrArg Subtype.val h

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
