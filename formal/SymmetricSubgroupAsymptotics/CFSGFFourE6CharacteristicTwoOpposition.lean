import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionLabels
import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoQuotientAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6NegativeRootUnits
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOppositionColumns

/-! The actual integral Geck opposition acts on both characteristic-two
spaces. Its root conjugacy is inherited from the same literal folded
matrices, with no original F4 faithfulness or simplicity assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoOpposition
open CFSGFFourSerreMatrices CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6GeckDiagramCovariance CFSGNormTwoGeckFieldOpposition
open CFSGNormTwoGeckFieldOppositionColumns CFSGFFourE6NegativeRootUnits
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoFixedQuotient
open CFSGFFourE6CharacteristicTwoQuotientAction CFSGFFourE6NormQuotientOppositionLabels
open CFSGSerreQuadraticMatrix

def oppositionVector (K:Type) [Field K] : Ambient K≃ₗ[K]Ambient K :=
  matrixLinearEquiv K (oppositionUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base K)

theorem oppositionVector_apply (K:Type) [Field K] (x:Ambient K) :
    oppositionVector K x=fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base K*ᵥx := rfl

theorem oppositionVector_involutive (K:Type) [Field K] :
    Function.Involutive (oppositionVector K) := by
  intro x
  rw [oppositionVector_apply,oppositionVector_apply,Matrix.mulVec_mulVec,
    fieldOmega_square,Matrix.one_mulVec]

theorem oppositionVector_single (K:Type) [Field K] (i:Index) :
    oppositionVector K (Pi.single i (1:K))=(Pi.single (oppositionIndex i) (1:K):Index→K) := by
  rw [oppositionVector_apply]
  cases i with
  | inl i=>exact omega_cartan CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K i
  | inr r=>exact omega_root CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K r

private theorem diagram_single (K:Type) [Field K] (i:Index) :
    diagramVector K (Pi.single i (1:K))=(Pi.single (diagramIndex i) (1:K):Index→K) := by
  funext j
  change (Pi.single i (1:K):Index→K) (diagramIndex.symm j)=
    (Pi.single (diagramIndex i) (1:K):Index→K) j
  simp only [Pi.single_apply,Equiv.symm_apply_eq]

theorem oppositionVector_commutes (K:Type) [Field K] (x:Ambient K) :
    oppositionVector K (diagramVector K x)=diagramVector K (oppositionVector K x) := by
  have he:(oppositionVector K).toLinearMap.comp (diagramVector K).toLinearMap=
      (diagramVector K).toLinearMap.comp (oppositionVector K).toLinearMap := by
    apply (Pi.basisFun K Index).ext
    intro i
    simp only [LinearMap.comp_apply,Pi.basisFun_apply]
    change oppositionVector K (diagramVector K (Pi.single i (1:K)))=
      diagramVector K (oppositionVector K (Pi.single i (1:K)))
    rw [diagram_single,oppositionVector_single,oppositionVector_single,diagram_single,
      oppositionIndex_diagram]
  exact LinearMap.congr_fun he x

def normOpposition (K:Type) [Field K] :
    characteristicNormImage K≃ₗ[K]characteristicNormImage K :=
  CFSGInvolutionNormImageAction.restrictEquiv (diagramVector K).toLinearMap
    (oppositionVector K) (oppositionVector_commutes K)

theorem normOpposition_val (K:Type) [Field K] (x:characteristicNormImage K) :
    (normOpposition K x).val=oppositionVector K x.val := rfl

def fixedOpposition (K:Type) [Field K] :
    characteristicFixedSpace K≃ₗ[K]characteristicFixedSpace K :=
  CFSGInvolutionFixedNormQuotientAction.fixedRestriction (diagramVector K).toLinearMap
    (oppositionVector K) (oppositionVector_commutes K)

theorem fixedOpposition_val (K:Type) [Field K] (x:characteristicFixedSpace K) :
    (fixedOpposition K x).val=oppositionVector K x.val := rfl

def quotientOpposition (K:Type) [Field K] :
    characteristicFixedQuotient K≃ₗ[K]characteristicFixedQuotient K :=
  CFSGInvolutionFixedNormQuotientAction.quotientRestriction (diagramVector K).toLinearMap
    (oppositionVector K) (oppositionVector_commutes K)

theorem quotientOpposition_mk (K:Type) [Field K] (x:characteristicFixedSpace K) :
    quotientOpposition K (Submodule.Quotient.mk x)=Submodule.Quotient.mk (fixedOpposition K x) := rfl

private theorem ambient_positive_conjugate (K:Type) [Field K] (i:Fin 4) (t:K) (x:Ambient K) :
    oppositionVector K (ambientAction K (foldedRoot K false i t) (oppositionVector K x))=
      ambientAction K (foldedRoot K true i t) x := by
  have hm:=congrArg (fun u:(Matrix Index Index K)ˣ=>(u:Matrix Index Index K))
    (folded_opposition K i t)
  change fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K*
    (canonicalRoot realizationData K false i t:Matrix Index Index K)*
    fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K=
      (canonicalRoot realizationData K true i t:Matrix Index Index K) at hm
  change fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K*ᵥ
    ((canonicalRoot realizationData K false i t:Matrix Index Index K)*ᵥ
      (fieldOmega CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base K*ᵥx))=
        (canonicalRoot realizationData K true i t:Matrix Index Index K)*ᵥx
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hm]

theorem ambient_positive_intertwines (K:Type) [Field K] (i:Fin 4) (t:K) (x:Ambient K) :
    oppositionVector K (ambientAction K (foldedRoot K false i t) x)=
      ambientAction K (foldedRoot K true i t) (oppositionVector K x) := by
  have h:=ambient_positive_conjugate K i t (oppositionVector K x)
  rw [oppositionVector_involutive] at h
  exact h

theorem norm_positive_intertwines (K:Type) [Field K] (i:Fin 4) (t:K)
    (x:characteristicNormImage K) :
    normOpposition K (normAction K (foldedRoot K false i t) x)=
      normAction K (foldedRoot K true i t) (normOpposition K x) := by
  apply Subtype.ext
  change oppositionVector K (ambientAction K (foldedRoot K false i t) x.val)=
    ambientAction K (foldedRoot K true i t) (oppositionVector K x.val)
  exact ambient_positive_intertwines K i t x.val

theorem quotient_positive_intertwines (K:Type) [Field K] (i:Fin 4) (t:K)
    (x:characteristicFixedQuotient K) :
    quotientOpposition K (quotientAction K (foldedRoot K false i t) x)=
      quotientAction K (foldedRoot K true i t) (quotientOpposition K x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  rw [quotientAction_mk,quotientOpposition_mk,quotientOpposition_mk,quotientAction_mk]
  congr 1
  apply Subtype.ext
  change oppositionVector K (ambientAction K (foldedRoot K false i t) v.val)=
    ambientAction K (foldedRoot K true i t) (oppositionVector K v.val)
  exact ambient_positive_intertwines K i t v.val

end SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoOpposition
