import SymmetricSubgroupAsymptotics.CFSGFFourE6NormActionFaithful
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleParameters
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Matrix coordinates of the actual faithful norm26 action. This is
an exact action homomorphism, so finite coordinate-word certificates can
return to the same folded group rather than a separate natural model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixAction
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormActionFaithful
open CFSGFFourE6NormQuotientCoordinateRootActions CFSGFFourE6NormQuotientSelectedCoefficients
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance
variable (K : Type) [Field K] [CharP K 2]

private def coordinateAction : canonicalElementaryGroup realizationData K→*
    Module.End K (PairIndex→K) where
  toFun g := (normCoordinateEquiv K).toLinearMap.comp
    ((normAction K g).toLinearMap.comp (normCoordinateEquiv K).symm.toLinearMap)
  map_one' := by
    apply LinearMap.ext
    intro x
    funext j
    change normCoordinateEquiv K (normAction K 1 ((normCoordinateEquiv K).symm x)) j=x j
    rw [map_one]
    exact congrArg (fun v : PairIndex→K=>v j) ((normCoordinateEquiv K).apply_symm_apply x)
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    funext j
    change normCoordinateEquiv K (normAction K (g*h) ((normCoordinateEquiv K).symm x)) j=
      normCoordinateEquiv K (normAction K g ((normCoordinateEquiv K).symm
        (normCoordinateEquiv K (normAction K h ((normCoordinateEquiv K).symm x))))) j
    rw [LinearEquiv.symm_apply_apply,map_mul]
    rfl

def normMatrixAction : canonicalElementaryGroup realizationData K→*Matrix PairIndex PairIndex K :=
  (LinearMap.toMatrixAlgEquiv' : Module.End K (PairIndex→K)≃ₐ[K]Matrix PairIndex PairIndex K).toMonoidHom.comp
    (coordinateAction K)

theorem normMatrixAction_entry (g : canonicalElementaryGroup realizationData K) (j k : PairIndex) :
    normMatrixAction K g j k=
      normCoordinateEquiv K (normAction K g (normBasis K k)) j := rfl

theorem normMatrixAction_positive_entry (i : Fin 4) (t : K) (j k : PairIndex) :
    normMatrixAction K (foldedRoot K false i t) j k=
      (Pi.single k (1:K) : PairIndex→K) j+t*(actualNormCoefficient (integerE i) j k:K)+
        t^2*(actualNormCoefficient (positiveSecondZ i) j k:K) := by
  rw [normMatrixAction_entry]
  exact normAction_coordinates_basis K i t j k

theorem normMatrixAction_injective [Finite K] : Function.Injective (normMatrixAction K) := by
  intro g h he
  apply normAction_injective K
  apply LinearEquiv.toLinearMap_injective
  apply (normBasis K).ext
  intro k
  apply (normCoordinateEquiv K).injective
  funext j
  exact congrArg (fun M : Matrix PairIndex PairIndex K=>M j k) he

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixAction
