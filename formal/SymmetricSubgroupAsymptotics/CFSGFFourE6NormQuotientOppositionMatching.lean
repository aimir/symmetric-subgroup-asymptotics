import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoOpposition
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientSelectedCovariance

/-! The SAME quotient-to-norm basis matching intertwines the actual
integral opposition. This is proved on literal fixed-unit representatives
and orbit-sum basis vectors, not inferred from root weights. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionMatching
open CFSGFFourSerreMatrices CFSGTwistedE6GeckDiagramCovariance
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6CharacteristicTwoFixedQuotient CFSGFFourE6CharacteristicTwoQuotientAction
open CFSGFFourE6CharacteristicTwoOpposition CFSGFFourE6NormQuotientOppositionLabels
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives
open CFSGFFourE6NormQuotientRootMatching CFSGFFourE6NormQuotientCoordinateRootActions
open CFSGFFourE6NormQuotientSelectedCovariance
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance

private theorem diagram_single (K:Type) [Field K] (i:Index) :
    diagramVector K (Pi.single i (1:K))=(Pi.single (diagramIndex i) (1:K):Index→K) := by
  funext j
  change (Pi.single i (1:K):Index→K) (diagramIndex.symm j)=
    (Pi.single (diagramIndex i) (1:K):Index→K) j
  simp only [Pi.single_apply,Equiv.symm_apply_eq]

theorem normOpposition_normBasis (K:Type) [Field K] [CharP K 2] (k:PairIndex) :
    normOpposition K (normBasis K k)=normBasis K (negativePair k) := by
  apply Subtype.ext
  simp only [normOpposition_val,normBasis_val,map_add,oppositionVector_commutes,
    oppositionVector_single]
  cases k with
  | inl i=>simp only [opposition_selected_inl]
  | inr r=>
    have htwice:diagramIndex (diagramIndex (selectedRepresentative (negativePair (Sum.inr r))))=
        selectedRepresentative (negativePair (Sum.inr r)) := diagramIndex_involutive _
    simpa only [opposition_selected_inr,diagram_single,htwice] using
      (add_comm
        (Pi.single (diagramIndex (selectedRepresentative (negativePair (Sum.inr r)))) (1:K):Index→K)
        (Pi.single (selectedRepresentative (negativePair (Sum.inr r))) (1:K):Index→K))

theorem fixedOpposition_fixedUnit (K:Type) [Field K] (k:PairIndex) :
    fixedOpposition K (fixedUnitVector K k)=fixedUnitVector K (negativePair k) := by
  apply Subtype.ext
  change oppositionVector K (Pi.single (fixedRepresentative (basisIndexDual k)) (1:K))=
    (Pi.single (fixedRepresentative (basisIndexDual (negativePair k))) (1:K):Index→K)
  rw [oppositionVector_single,opposition_fixed_dual]

theorem quotientOpposition_fixedUnit (K:Type) [Field K] (k:PairIndex) :
    quotientOpposition K (Submodule.Quotient.mk (fixedUnitVector K k))=
      Submodule.Quotient.mk (fixedUnitVector K (negativePair k)) := by
  rw [quotientOpposition_mk,fixedOpposition_fixedUnit]

theorem quotientToNorm_opposition (K:Type) [Field K] [CharP K 2]
    (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientOpposition K x)=normOpposition K (quotientToNorm K x) := by
  have he:(quotientToNorm K).toLinearMap.comp (quotientOpposition K).toLinearMap=
      (normOpposition K).toLinearMap.comp (quotientToNorm K).toLinearMap := by
    apply ((Pi.basisFun K PairIndex).map (quotientPairCoordinates K).symm).ext
    intro k
    simp only [Module.Basis.map_apply,Pi.basisFun_apply]
    change quotientToNorm K (quotientOpposition K ((quotientPairCoordinates K).symm (Pi.single k (1:K))))=
      normOpposition K (quotientToNorm K ((quotientPairCoordinates K).symm (Pi.single k (1:K))))
    rw [quotientPairCoordinates_symm_single,quotientOpposition_fixedUnit,
      quotientToNorm_fixedUnit,quotientToNorm_fixedUnit,normOpposition_normBasis]
  exact LinearMap.congr_fun he x

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionMatching
