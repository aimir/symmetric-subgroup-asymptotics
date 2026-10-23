import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoordinateRootActions

/-! Selected genuine covariance of the two actual 26-dimensional
actions: short node 1 maps to long node 2 with squared parameter, and
long node 2 maps to short node 1 with unchanged parameter. This pilot
does not assert an exceptional automorphism of the original F4 model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientSelectedCovariance
open CFSGFFourSerreMatrices
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6CharacteristicTwoFixedQuotient CFSGFFourE6CharacteristicTwoQuotientAction
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormQuotientSelectedCoefficients
open CFSGFFourE6NormQuotientCoordinateRootActions
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance

def quotientToNorm (K:Type) [Field K] [CharP K 2] :
    characteristicFixedQuotient K≃ₗ[K]characteristicNormImage K :=
  (quotientPairCoordinates K).trans (normCoordinateEquiv K).symm

theorem normCoordinate_quotientToNorm (K:Type) [Field K] [CharP K 2]
    (x:characteristicFixedQuotient K) :
    normCoordinateEquiv K (quotientToNorm K x)=quotientPairCoordinates K x :=
  (normCoordinateEquiv K).apply_symm_apply (quotientPairCoordinates K x)

theorem quotientToNorm_fixedUnit (K:Type) [Field K] [CharP K 2] (k:PairIndex) :
    quotientToNorm K (Submodule.Quotient.mk (fixedUnitVector K k))=normBasis K k := by
  apply (normCoordinateEquiv K).injective
  rw [normCoordinate_quotientToNorm,quotientPairCoordinates_fixedUnit]
  simp only [normBasis,Module.Basis.map_apply,Pi.basisFun_apply,LinearEquiv.apply_symm_apply]

theorem short_covariance_fixedUnit (K:Type) [Field K] [CharP K 2] (t:K) (k:PairIndex) :
    quotientToNorm K (quotientAction K (foldedRoot K false 1 t)
      (Submodule.Quotient.mk (fixedUnitVector K k)))=
        normAction K (foldedRoot K false 2 (t^2)) (normBasis K k) := by
  apply (normCoordinateEquiv K).injective
  rw [normCoordinate_quotientToNorm]
  funext j
  change quotientPairCoordinates K (quotientAction K (foldedRoot K false 1 t)
    (Submodule.Quotient.mk (fixedUnitVector K k))) j=
      normCoordinateEquiv K (normAction K (foldedRoot K false 2 (t^2)) (normBasis K k)) j
  rw [quotientAction_coordinates_unit,normAction_coordinates_basis,
    cast_short_quotient_linear_zero,cast_short_quotient_quadratic,cast_long_norm_quadratic_zero]
  simp only [mul_zero,add_zero]

theorem long_covariance_fixedUnit (K:Type) [Field K] [CharP K 2] (t:K) (k:PairIndex) :
    quotientToNorm K (quotientAction K (foldedRoot K false 2 t)
      (Submodule.Quotient.mk (fixedUnitVector K k)))=
        normAction K (foldedRoot K false 1 t) (normBasis K k) := by
  apply (normCoordinateEquiv K).injective
  rw [normCoordinate_quotientToNorm]
  funext j
  change quotientPairCoordinates K (quotientAction K (foldedRoot K false 2 t)
    (Submodule.Quotient.mk (fixedUnitVector K k))) j=
      normCoordinateEquiv K (normAction K (foldedRoot K false 1 t) (normBasis K k)) j
  rw [quotientAction_coordinates_unit,normAction_coordinates_basis,
    cast_long_quotient_linear,cast_long_quotient_quadratic]

private theorem linear_eq_of_fixedUnits (K:Type) [Field K] [CharP K 2]
    (f g:characteristicFixedQuotient K→ₗ[K]characteristicNormImage K)
    (he:∀k:PairIndex,f (Submodule.Quotient.mk (fixedUnitVector K k))=
      g (Submodule.Quotient.mk (fixedUnitVector K k))) : f=g := by
  have hcomp:f.comp (quotientPairCoordinates K).symm.toLinearMap=
      g.comp (quotientPairCoordinates K).symm.toLinearMap := by
    apply (Pi.basisFun K PairIndex).ext
    intro k
    simp only [LinearMap.comp_apply,Pi.basisFun_apply]
    change f ((quotientPairCoordinates K).symm (Pi.single k (1:K)))=
      g ((quotientPairCoordinates K).symm (Pi.single k (1:K)))
    rw [quotientPairCoordinates_symm_single]
    exact he k
  apply LinearMap.ext
  intro x
  have hx:=LinearMap.congr_fun hcomp (quotientPairCoordinates K x)
  change f ((quotientPairCoordinates K).symm (quotientPairCoordinates K x))=
    g ((quotientPairCoordinates K).symm (quotientPairCoordinates K x)) at hx
  simpa only [LinearEquiv.symm_apply_apply] using hx

theorem selected_short_covariance (K:Type) [Field K] [CharP K 2]
    (t:K) (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K false 1 t) x)=
      normAction K (foldedRoot K false 2 (t^2)) (quotientToNorm K x) := by
  have he:=linear_eq_of_fixedUnits K
    ((quotientToNorm K).toLinearMap.comp (quotientAction K (foldedRoot K false 1 t)).toLinearMap)
    ((normAction K (foldedRoot K false 2 (t^2))).toLinearMap.comp (quotientToNorm K).toLinearMap)
    (fun k=>by
      change quotientToNorm K (quotientAction K (foldedRoot K false 1 t)
        (Submodule.Quotient.mk (fixedUnitVector K k)))=
          normAction K (foldedRoot K false 2 (t^2))
            (quotientToNorm K (Submodule.Quotient.mk (fixedUnitVector K k)))
      rw [quotientToNorm_fixedUnit]
      exact short_covariance_fixedUnit K t k)
  exact LinearMap.congr_fun he x

theorem selected_long_covariance (K:Type) [Field K] [CharP K 2]
    (t:K) (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K false 2 t) x)=
      normAction K (foldedRoot K false 1 t) (quotientToNorm K x) := by
  have he:=linear_eq_of_fixedUnits K
    ((quotientToNorm K).toLinearMap.comp (quotientAction K (foldedRoot K false 2 t)).toLinearMap)
    ((normAction K (foldedRoot K false 1 t)).toLinearMap.comp (quotientToNorm K).toLinearMap)
    (fun k=>by
      change quotientToNorm K (quotientAction K (foldedRoot K false 2 t)
        (Submodule.Quotient.mk (fixedUnitVector K k)))=
          normAction K (foldedRoot K false 1 t)
            (quotientToNorm K (Submodule.Quotient.mk (fixedUnitVector K k)))
      rw [quotientToNorm_fixedUnit]
      exact long_covariance_fixedUnit K t k)
  exact LinearMap.congr_fun he x

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientSelectedCovariance
