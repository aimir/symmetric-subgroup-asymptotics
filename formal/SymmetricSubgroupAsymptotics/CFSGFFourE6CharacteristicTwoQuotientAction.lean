import SymmetricSubgroupAsymptotics.CFSGInvolutionFixedNormQuotientAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoFixedQuotient

/-! The same literal folded F4 matrices act on the fixed-space quotient.
The signed simple-root formula retains both integral root coefficients.
No exceptional covariance or original-source faithfulness is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoQuotientAction
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoFixedQuotient
open CFSGFFourE6FixedIndexRepresentatives

def fixedActionVector (K:Type) [Field K] (g:canonicalElementaryGroup realizationData K)
    (x:characteristicFixedSpace K) : characteristicFixedSpace K :=
  CFSGInvolutionFixedNormQuotientAction.fixedRestriction (diagramVector K).toLinearMap
    (ambientAction K g) (ambientAction_commutes K g) x

theorem fixedActionVector_val (K:Type) [Field K] (g:canonicalElementaryGroup realizationData K)
    (x:characteristicFixedSpace K) :
    (fixedActionVector K g x).val=(g.val:Matrix Index Index K)*ᵥx.val := rfl

def quotientAction (K:Type) [Field K] :
    canonicalElementaryGroup realizationData K→*
      (characteristicFixedQuotient K≃ₗ[K]characteristicFixedQuotient K) :=
  CFSGInvolutionFixedNormQuotientAction.quotientAction (diagramVector K).toLinearMap
    (ambientAction K) (ambientAction_commutes K)

theorem quotientAction_mk (K:Type) [Field K] (g:canonicalElementaryGroup realizationData K)
    (x:characteristicFixedSpace K) :
    quotientAction K g (Submodule.Quotient.mk x)=
      Submodule.Quotient.mk (fixedActionVector K g x) := rfl

theorem quotientAction_root_coordinates (K:Type) [Field K] [CharP K 2]
    (neg:Bool) (i:Fin 4) (t:K) (x:characteristicFixedSpace K) (j:FixedLabel) :
    quotientCoordinateEquiv K
      (quotientAction K (foldedRoot K neg i t) (Submodule.Quotient.mk x)) j=
      ((1+t • fieldRoot realizationData K neg i+t^2 • fieldSecond realizationData K neg i)*ᵥx.val)
        (fixedRepresentative j) := by
  rw [quotientAction_mk,quotientCoordinateEquiv_mk]
  rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoQuotientAction
