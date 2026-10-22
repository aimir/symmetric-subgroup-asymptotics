import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalA2
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixActions
import SymmetricSubgroupAsymptotics.CFSGSerreFixedRootElements
import SymmetricSubgroupAsymptotics.CFSGSerreOrdinaryTwistModels

/-!
# The selected A2 action on its actual natural-matrix image

The original Serre group acts on the image of its SAME integral tensor
realization. Its range equals the conjugation-action range of the explicit
three-dimensional root matrices. Restriction to the original twisted-A2
fixed subgroup and its actual commutator needs no group identification.
No simplicity, faithfulness or unitary-form condition is assumed here.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

def a2RootMatrix (K : Type) [Field K] (neg : Bool) (i : Fin 2) : Mat K 2 :=
  if neg then negative K 2 i else positive K 2 i

theorem realizationDataA2_fieldRoot (K : Type) [Field K] (neg : Bool) (i : Fin 2) :
    CFSGSerreSquareZeroMatrix.fieldRoot realizationDataA2 K neg i = a2RootMatrix K neg i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (positive ℤ 2 i) = positive K 2 i
    exact map_positive ℤ 2 (Int.castRingHom K) i
  · change (Int.castRingHom K).mapMatrix (negative ℤ 2 i) = negative K 2 i
    exact map_negative ℤ 2 (Int.castRingHom K) i

theorem a2RootMatrix_sq_zero (K : Type) [Field K] (neg : Bool) (i : Fin 2) :
    a2RootMatrix K neg i * a2RootMatrix K neg i = 0 := by
  rw [← realizationDataA2_fieldRoot]
  exact CFSGSerreSquareZeroMatrix.fieldRoot_sq_zero realizationDataA2 K neg i

def a2RootUnit (K : Type) [Field K] (neg : Bool) (i : Fin 2) (t : K) : (Mat K 2)ˣ where
  val := 1 + t • a2RootMatrix K neg i
  inv := 1 - t • a2RootMatrix K neg i
  val_inv := CFSGSquareZeroConjugation.transvection_mul_inverse t _
    (a2RootMatrix_sq_zero K neg i)
  inv_val := CFSGSquareZeroConjugation.inverse_mul_transvection t _
    (a2RootMatrix_sq_zero K neg i)

theorem a2RootUnit_val (K : Type) [Field K] (neg : Bool) (i : Fin 2) (t : K) :
    (a2RootUnit K neg i t : Mat K 2) =
      1 + t • CFSGSerreSquareZeroMatrix.fieldRoot realizationDataA2 K neg i := by
  rw [realizationDataA2_fieldRoot]
  rfl

theorem a2RootUnit_inv_val (K : Type) [Field K] (neg : Bool) (i : Fin 2) (t : K) :
    (↑((a2RootUnit K neg i t)⁻¹) : Mat K 2) =
      1 - t • CFSGSerreSquareZeroMatrix.fieldRoot realizationDataA2 K neg i := by
  rw [realizationDataA2_fieldRoot]
  rfl

abbrev NaturalA2Image (K : Type) [Field K] :=
  (CFSGSerreSquareZeroMatrix.baseChange realizationDataA2 K).range

def naturalA2Action (K : Type) [Field K] :
    Model (CartanMatrix.A 2) K →* (NaturalA2Image K ≃ₗ[K] NaturalA2Image K) :=
  CFSGSerreSquareZeroMatrix.imageRepresentation realizationDataA2 K

def elementaryA2Action (K : Type) [Field K] :
    CFSGSerreSquareZeroMatrix.elementaryGroup K (a2RootUnit K) →*
      (NaturalA2Image K ≃ₗ[K] NaturalA2Image K) :=
  CFSGSerreSquareZeroMatrix.elementaryImageAction realizationDataA2 K
    (a2RootUnit K) (a2RootUnit_val K) (a2RootUnit_inv_val K)

theorem naturalA2Action_ranges_eq (K : Type) [Field K] :
    (naturalA2Action K).range = (elementaryA2Action K).range :=
  CFSGSerreSquareZeroMatrix.action_ranges_eq realizationDataA2 K
    (a2RootUnit K) (a2RootUnit_val K) (a2RootUnit_inv_val K)

def twistedA2FixedAction (q : CFSG.PrimePower) :
    fixedSubgroup (CartanMatrix.A 2) (q.Extension 2) CFSG.Models.reverseNode
      (fun _ => q.order) →*
      (NaturalA2Image (q.Extension 2) ≃ₗ[q.Extension 2] NaturalA2Image (q.Extension 2)) :=
  (naturalA2Action (q.Extension 2)).comp
    (CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.A 2) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order))

def twistedA2DerivedAction (q : CFSG.PrimePower) :
    commutator (fixedSubgroup (CartanMatrix.A 2) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order)) →*
      (NaturalA2Image (q.Extension 2) ≃ₗ[q.Extension 2] NaturalA2Image (q.Extension 2)) :=
  (naturalA2Action (q.Extension 2)).comp
    (CFSGSerreFixedRootElements.derivedToModel (CartanMatrix.A 2) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order))

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
