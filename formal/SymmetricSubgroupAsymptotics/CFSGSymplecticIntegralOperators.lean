import SymmetricSubgroupAsymptotics.CFSGSymplecticIntegralRepresentation
import SymmetricSubgroupAsymptotics.CFSGIntegralSquareZeroOperators

/-! The genuine integral type-C representation intertwines every actual
source divided power with an explicit integral matrix polynomial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

def rootMatrix (R : Type*) [CommRing R] (r : ℕ) (neg : Bool) (i : Fin r) : Mat R r :=
  if neg then negative R r i else positive R r i

theorem map_rootMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : ℕ) (neg : Bool) (i : Fin r) :
    f.mapMatrix (rootMatrix R r neg i) = rootMatrix S r neg i := by
  cases neg <;> simp only [rootMatrix, Bool.false_eq_true, if_false, if_true,
    map_positive, map_negative]

theorem rootMatrix_sq_zero (R : Type*) [CommRing R] (r : ℕ) (neg : Bool) (i : Fin r) :
    rootMatrix R r neg i * rootMatrix R r neg i = 0 := by
  cases neg
  · simpa only [rootMatrix, Bool.false_eq_true, if_false, pow_two] using positive_sq_zero R r i
  · simpa only [rootMatrix, if_true, pow_two] using negative_sq_zero R r i

theorem rationalRepresentation_rootVector (r : ℕ) (neg : Bool) (i : Fin r) :
    rationalSymplecticRepresentation r (rootVector (CartanMatrix.C r).transpose neg i) =
      rootMatrix ℚ r neg i := by
  cases neg
  · exact rationalSymplecticRepresentation_E r i
  · exact rationalSymplecticRepresentation_F r i

theorem integralRepresentation_operator (r : ℕ) (neg : Bool) (i : Fin r) (k : ℕ)
    (x : integralLattice (CartanMatrix.C r).transpose) :
    integralSymplecticRepresentation r
      (integralOperator (CartanMatrix.C r).transpose neg i k x) =
      CFSGIntegralSquareZeroOperators.operator ℤ (rootMatrix ℤ r neg i) k
        (integralSymplecticRepresentation r x) := by
  apply intMatrixLinearMap_injective r
  rw [integralSymplecticRepresentation_cast]
  change rationalSymplecticRepresentation r
    (dividedPower (CartanMatrix.C r).transpose neg i k x.val) =
    (Int.castRingHom ℚ).mapMatrix
      (CFSGIntegralSquareZeroOperators.operator ℤ (rootMatrix ℤ r neg i) k
        (integralSymplecticRepresentation r x))
  rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,
    rationalRepresentation_rootVector]
  rw [CFSGIntegralSquareZeroOperators.rational_operator _ _ (rootMatrix_sq_zero ℚ r neg i),
    CFSGIntegralSquareZeroOperators.map_operator, map_rootMatrix]
  rw [CFSGIntegralSquareZeroOperators.operator_changeScalars ℤ ℚ]
  exact congrArg (CFSGIntegralSquareZeroOperators.operator ℚ (rootMatrix ℚ r neg i) k)
    (integralSymplecticRepresentation_cast r x).symm

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
