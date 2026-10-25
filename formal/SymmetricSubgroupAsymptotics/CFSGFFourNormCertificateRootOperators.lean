import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixNegativeAction

/-! Computable signed root operators on the selected 26 labels equal
the entries of the same actual folded norm action over every field of
characteristic two. No word or period certificate is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateRootOperators
open CFSGFFourNormCertificateCoordinates CFSGFFourE6NormPairRepresentatives
open CFSGFFourE6NormQuotientOppositionLabels CFSGFFourE6NormQuotientCoefficientPilot
open CFSGFFourE6NormSimpleCoefficientPilot CFSGFFourE6NormSimpleParameters
open CFSGFFourE6NormMatrixAction CFSGFFourE6NormMatrixNegativeAction
open CFSGFFourE6CharacteristicTwoNormImage
private instance : DecidableEq PairIndex := by unfold PairIndex; infer_instance

def signedCoordinate (neg : Bool) (j : Fin 26) : PairIndex :=
  if neg then negativePair (coordinateEquiv j) else coordinateEquiv j

def firstCoefficient (neg : Bool) (i : Fin 4) (j k : Fin 26) : ℤ :=
  normCoefficient (firstEntry i) (signedCoordinate neg j) (signedCoordinate neg k)

def secondCoefficient (neg : Bool) (i : Fin 4) (j k : Fin 26) : ℤ :=
  normCoefficient (quadraticEntry i) (signedCoordinate neg j) (signedCoordinate neg k)

def rootOperator (K : Type) [CommRing K] (neg : Bool) (i : Fin 4) (t : K) :
    Matrix (Fin 26) (Fin 26) K := fun j k =>
  (if signedCoordinate neg j = signedCoordinate neg k then 1 else 0) +
    t*(firstCoefficient neg i j k : K) + t^2*(secondCoefficient neg i j k : K)

theorem actual_root_entry (K : Type) [Field K] [CharP K 2]
    (neg : Bool) (i : Fin 4) (t : K) (j k : Fin 26) :
    normMatrixAction K (foldedRoot K neg i t) (coordinateEquiv j) (coordinateEquiv k) =
      rootOperator K neg i t j k := by
  cases neg with
  | false =>
    rw [normMatrixAction_positive_entry,first_norm_coefficient,quadratic_norm_coefficient]
    by_cases h : coordinateEquiv j = coordinateEquiv k <;>
      simp [rootOperator,firstCoefficient,secondCoefficient,signedCoordinate,Pi.single_apply,h]
  | true =>
    rw [normMatrixAction_negative_entry,normMatrixAction_positive_entry,
      first_norm_coefficient,quadratic_norm_coefficient]
    by_cases h : negativePair (coordinateEquiv j) = negativePair (coordinateEquiv k) <;>
      simp [rootOperator,firstCoefficient,secondCoefficient,signedCoordinate,Pi.single_apply,h]

end SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateRootOperators
