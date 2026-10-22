import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalSerre
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixActions
import SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels

/-!
# The original arbitrary-rank Serre A action on its actual matrix image

The symbolic rational representation installs the checked integral and
divided-power descent. Original roots and explicit natural root matrices
give exactly the same conjugation-action range. The original twisted fixed
and derived groups act by restriction of this SAME action. Nothing here
identifies a fixed subgroup with a unitary matrix group or presumes that
the original source action is faithful.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

def naturalIntegerGenerator (r : ℕ) : CartanMatrix.Generators (Fin r) → Mat ℤ r
  | .H i => cartan ℤ r i
  | .E i => positive ℤ r i
  | .F i => negative ℤ r i

def realizationData (r : ℕ) :
    CFSGSerreSquareZeroMatrix.Data (CartanMatrix.A r) (Fin (r + 1)) where
  rational := rationalNatural r
  integerGenerator := naturalIntegerGenerator r
  generator_cast := by
    intro g
    cases g with
    | H i => simpa only [naturalIntegerGenerator, rationalNatural_H] using
        map_cartan ℤ r (Int.castRingHom ℚ) i
    | E i => simpa only [naturalIntegerGenerator, rationalNatural_E] using
        map_positive ℤ r (Int.castRingHom ℚ) i
    | F i => simpa only [naturalIntegerGenerator, rationalNatural_F] using
        map_negative ℤ r (Int.castRingHom ℚ) i
  root_square_zero := by
    intro neg i
    cases neg
    · exact positive_sq_zero ℤ r i
    · exact negative_sq_zero ℤ r i

def rootMatrix (R : Type*) [CommRing R] (r : ℕ) (neg : Bool) (i : Fin r) : Mat R r :=
  if neg then negative R r i else positive R r i

theorem realizationData_fieldRoot (R : Type*) [CommRing R] (r : ℕ)
    (neg : Bool) (i : Fin r) :
    CFSGSerreSquareZeroMatrix.fieldRoot (realizationData r) R neg i = rootMatrix R r neg i := by
  cases neg
  · change (Int.castRingHom R).mapMatrix (positive ℤ r i) = positive R r i
    exact map_positive ℤ r (Int.castRingHom R) i
  · change (Int.castRingHom R).mapMatrix (negative ℤ r i) = negative R r i
    exact map_negative ℤ r (Int.castRingHom R) i

theorem rootMatrix_sq_zero (R : Type*) [CommRing R] (r : ℕ) (neg : Bool) (i : Fin r) :
    rootMatrix R r neg i * rootMatrix R r neg i = 0 := by
  rw [← realizationData_fieldRoot]
  exact CFSGSerreSquareZeroMatrix.fieldRoot_sq_zero (realizationData r) R neg i

def naturalRootUnit (R : Type*) [CommRing R] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : R) : (Mat R r)ˣ where
  val := 1 + t • rootMatrix R r neg i
  inv := 1 - t • rootMatrix R r neg i
  val_inv := CFSGSquareZeroConjugation.transvection_mul_inverse t _
    (rootMatrix_sq_zero R r neg i)
  inv_val := CFSGSquareZeroConjugation.inverse_mul_transvection t _
    (rootMatrix_sq_zero R r neg i)

theorem naturalRootUnit_val (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    (naturalRootUnit K r neg i t : Mat K r) =
      1 + t • CFSGSerreSquareZeroMatrix.fieldRoot (realizationData r) K neg i := by
  rw [realizationData_fieldRoot]
  rfl

theorem naturalRootUnit_inv_val (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    (↑((naturalRootUnit K r neg i t)⁻¹) : Mat K r) =
      1 - t • CFSGSerreSquareZeroMatrix.fieldRoot (realizationData r) K neg i := by
  rw [realizationData_fieldRoot]
  rfl

abbrev NaturalImage (K : Type) [Field K] (r : ℕ) :=
  (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) K).range

def naturalAction (K : Type) [Field K] (r : ℕ) :
    Model (CartanMatrix.A r) K →* (NaturalImage K r ≃ₗ[K] NaturalImage K r) :=
  CFSGSerreSquareZeroMatrix.imageRepresentation (realizationData r) K

def naturalElementaryAction (K : Type) [Field K] (r : ℕ) :
    CFSGSerreSquareZeroMatrix.elementaryGroup K (naturalRootUnit K r) →*
      (NaturalImage K r ≃ₗ[K] NaturalImage K r) :=
  CFSGSerreSquareZeroMatrix.elementaryImageAction (realizationData r) K
    (naturalRootUnit K r) (naturalRootUnit_val K r) (naturalRootUnit_inv_val K r)

theorem naturalAction_ranges_eq (K : Type) [Field K] (r : ℕ) :
    (naturalAction K r).range = (naturalElementaryAction K r).range :=
  CFSGSerreSquareZeroMatrix.action_ranges_eq (realizationData r) K
    (naturalRootUnit K r) (naturalRootUnit_val K r) (naturalRootUnit_inv_val K r)

theorem naturalAction_root (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) (y : NaturalImage K r) :
    (naturalAction K r (CFSGSerreModelRootGeneration.modelRoot (CartanMatrix.A r)
      K neg i t) y).val =
      (1 + t • rootMatrix K r neg i) * y.val * (1 - t • rootMatrix K r neg i) := by
  simpa only [realizationData_fieldRoot] using
    CFSGSerreSquareZeroMatrix.imageRepresentation_root (realizationData r) K neg i t y

def twistedFixedAction (r : ℕ) (q : CFSG.PrimePower) :
    fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode
      (fun _ => q.order) →*
      (NaturalImage (q.Extension 2) r ≃ₗ[q.Extension 2] NaturalImage (q.Extension 2) r) :=
  (naturalAction (q.Extension 2) r).comp
    (CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order))

def twistedDerivedAction (r : ℕ) (q : CFSG.PrimePower) :
    commutator (fixedSubgroup (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order)) →*
      (NaturalImage (q.Extension 2) r ≃ₗ[q.Extension 2] NaturalImage (q.Extension 2) r) :=
  (naturalAction (q.Extension 2) r).comp
    (CFSGSerreFixedRootElements.derivedToModel (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order))

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
