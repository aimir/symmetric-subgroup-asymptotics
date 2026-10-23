import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoQuotientAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientSelectedCoefficients

/-! Coordinate formulas for the actual two characteristic-two actions.
The quotient basis is represented by literal fixed-index unit vectors;
the norm basis is the already checked orbit-sum basis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoordinateRootActions
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix CFSGNormTwoRootPairing
open CFSGTwistedE6GeckDiagramCovariance
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6CharacteristicTwoFixedQuotient CFSGFFourE6CharacteristicTwoQuotientAction
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives
open CFSGFFourE6NormQuotientRootMatching CFSGFFourE6NormQuotientSelectedCoefficients
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance

def quotientPairCoordinates (K:Type) [Field K] [CharP K 2] :
    characteristicFixedQuotient K≃ₗ[K](PairIndex→K) :=
  (quotientCoordinateEquiv K).trans (LinearEquiv.funCongrLeft K K basisIndexDual)

private theorem diagramVector_single (K:Type) [Field K] (i:Index) :
    diagramVector K (Pi.single i (1:K))=(Pi.single (diagramIndex i) (1:K):Index→K) := by
  funext j
  change (Pi.single i (1:K):Index→K) (diagramIndex.symm j)=
    (Pi.single (diagramIndex i) (1:K):Index→K) j
  simp only [Pi.single_apply,Equiv.symm_apply_eq] <;> split_ifs <;> rfl

def fixedUnitVector (K:Type) [Field K] (k:PairIndex) : characteristicFixedSpace K :=
  ⟨Pi.single (fixedRepresentative (basisIndexDual k)) 1,by
    change diagramVector K (Pi.single (fixedRepresentative (basisIndexDual k)) 1)=_
    rw [diagramVector_single,fixedRepresentative_fixed]
    rfl⟩

theorem quotientPairCoordinates_fixedUnit (K:Type) [Field K] [CharP K 2] (k:PairIndex) :
    quotientPairCoordinates K (Submodule.Quotient.mk (fixedUnitVector K k))=Pi.single k 1 := by
  funext j
  change quotientCoordinateEquiv K (Submodule.Quotient.mk (fixedUnitVector K k))
    (basisIndexDual j)=(Pi.single k (1:K):PairIndex→K) j
  rw [quotientCoordinateEquiv_mk]
  have he:fixedRepresentative (basisIndexDual j)=fixedRepresentative (basisIndexDual k) ↔ j=k :=
    (fixedRepresentative_injective.comp basisIndexDual.injective).eq_iff
  change (Pi.single (fixedRepresentative (basisIndexDual k)) (1:K):Index→K)
    (fixedRepresentative (basisIndexDual j))=(Pi.single k (1:K):PairIndex→K) j
  simp only [Pi.single_apply,he] <;> split_ifs <;> rfl

theorem quotientPairCoordinates_symm_single (K:Type) [Field K] [CharP K 2] (k:PairIndex) :
    (quotientPairCoordinates K).symm (Pi.single k 1)=Submodule.Quotient.mk (fixedUnitVector K k) := by
  have h:=congrArg (quotientPairCoordinates K).symm (quotientPairCoordinates_fixedUnit K k)
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

private theorem norm_identity (K:Type) [Field K] (j k:PairIndex) :
    (1:Matrix Index Index K) (selectedRepresentative j) (selectedRepresentative k)+
      (1:Matrix Index Index K) (selectedRepresentative j) (diagramIndex (selectedRepresentative k))=
        (Pi.single k (1:K):PairIndex→K) j := by
  have he:selectedRepresentative j=selectedRepresentative k ↔ j=k:=selectedRepresentative_injective.eq_iff
  simp only [Matrix.one_apply,if_neg (selectedRepresentative_disjoint j k),add_zero,he,Pi.single_apply]

private theorem quotient_identity (K:Type) [Field K] (j k:PairIndex) :
    (1:Matrix Index Index K) (fixedRepresentative (basisIndexDual j))
      (fixedRepresentative (basisIndexDual k))=(Pi.single k (1:K):PairIndex→K) j := by
  have he:fixedRepresentative (basisIndexDual j)=fixedRepresentative (basisIndexDual k) ↔ j=k :=
    (fixedRepresentative_injective.comp basisIndexDual.injective).eq_iff
  simp only [Matrix.one_apply,he,Pi.single_apply]

theorem normAction_coordinates_basis (K:Type) [Field K] [CharP K 2]
    (i:Fin 4) (t:K) (j k:PairIndex) :
    normCoordinateEquiv K (normAction K (foldedRoot K false i t) (normBasis K k)) j=
      (Pi.single k (1:K):PairIndex→K) j+t*(actualNormCoefficient (integerE i) j k:K)+
        t^2*(actualNormCoefficient (positiveSecondZ i) j k:K) := by
  rw [normCoordinateEquiv_apply,normAction_val,normBasis_val,diagramVector_single,
    Matrix.mulVec_add,Matrix.mulVec_single_one,Matrix.mulVec_single_one]
  change (1+t • fieldRoot realizationData K false i+t^2 • fieldSecond realizationData K false i)
      (selectedRepresentative j) (selectedRepresentative k)+
    (1+t • fieldRoot realizationData K false i+t^2 • fieldSecond realizationData K false i)
      (selectedRepresentative j) (diagramIndex (selectedRepresentative k))=_
  have hE (r s:Index):fieldRoot realizationData K false i r s=(integerE i r s:K):=rfl
  have hD (r s:Index):fieldSecond realizationData K false i r s=(positiveSecondZ i r s:K):=rfl
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hE,hD,
    actualNormCoefficient,Int.cast_add]
  calc
    _=((1:Matrix Index Index K) (selectedRepresentative j) (selectedRepresentative k)+
        (1:Matrix Index Index K) (selectedRepresentative j) (diagramIndex (selectedRepresentative k)))+
      t*((integerE i (selectedRepresentative j) (selectedRepresentative k):K)+
        (integerE i (selectedRepresentative j) (diagramIndex (selectedRepresentative k)):K))+
      t^2*((positiveSecondZ i (selectedRepresentative j) (selectedRepresentative k):K)+
        (positiveSecondZ i (selectedRepresentative j) (diagramIndex (selectedRepresentative k)):K)) := by ring
    _= _ := by rw [norm_identity]

theorem quotientAction_coordinates_unit (K:Type) [Field K] [CharP K 2]
    (i:Fin 4) (t:K) (j k:PairIndex) :
    quotientPairCoordinates K
      (quotientAction K (foldedRoot K false i t) (Submodule.Quotient.mk (fixedUnitVector K k))) j=
      (Pi.single k (1:K):PairIndex→K) j+t*(actualQuotientCoefficient (integerE i) j k:K)+
        t^2*(actualQuotientCoefficient (positiveSecondZ i) j k:K) := by
  change quotientCoordinateEquiv K
    (quotientAction K (foldedRoot K false i t) (Submodule.Quotient.mk (fixedUnitVector K k)))
      (basisIndexDual j)=_
  rw [quotientAction_root_coordinates]
  change ((1+t • fieldRoot realizationData K false i+t^2 • fieldSecond realizationData K false i)*ᵥ
    Pi.single (fixedRepresentative (basisIndexDual k)) 1) (fixedRepresentative (basisIndexDual j))=_
  rw [Matrix.mulVec_single_one]
  change (1+t • fieldRoot realizationData K false i+t^2 • fieldSecond realizationData K false i)
    (fixedRepresentative (basisIndexDual j)) (fixedRepresentative (basisIndexDual k))=_
  have hE (r s:Index):fieldRoot realizationData K false i r s=(integerE i r s:K):=rfl
  have hD (r s:Index):fieldSecond realizationData K false i r s=(positiveSecondZ i r s:K):=rfl
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hE,hD,
    actualQuotientCoefficient,quotient_identity]

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoordinateRootActions
