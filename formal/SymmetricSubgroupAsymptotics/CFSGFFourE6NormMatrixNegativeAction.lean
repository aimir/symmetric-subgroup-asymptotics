import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionMatching

/-! Signed coordinate transport for the SAME faithful norm26 action.
Actual integral opposition gives the negative matrix by the already
checked involution of its orbit-sum basis labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixNegativeAction
open CFSGFFourE6NormMatrixAction CFSGFFourE6CharacteristicTwoNormImage
open CFSGFFourE6CharacteristicTwoNormBasis CFSGFFourE6NormPairRepresentatives
open CFSGFFourE6CharacteristicTwoOpposition CFSGFFourE6NormQuotientOppositionLabels
open CFSGFFourE6NormQuotientOppositionMatching
variable (K : Type) [Field K] [CharP K 2]
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance

private theorem coordinate_basis (k : PairIndex) :
    normCoordinateEquiv K (normBasis K k)=Pi.single k 1 := by
  change normCoordinateEquiv K ((normCoordinateEquiv K).symm (Pi.single k 1))=_
  exact (normCoordinateEquiv K).apply_symm_apply _

theorem normOpposition_coordinates (x : characteristicNormImage K) (j : PairIndex) :
    normCoordinateEquiv K (normOpposition K x) j=
      normCoordinateEquiv K x (negativePair j) := by
  have he : (LinearMap.proj j).comp ((normCoordinateEquiv K).toLinearMap.comp
        (normOpposition K).toLinearMap)=
      (LinearMap.proj (negativePair j)).comp (normCoordinateEquiv K).toLinearMap := by
    apply (normBasis K).ext
    intro k
    change normCoordinateEquiv K (normOpposition K (normBasis K k)) j=
      normCoordinateEquiv K (normBasis K k) (negativePair j)
    rw [normOpposition_normBasis,coordinate_basis,coordinate_basis]
    have hiff : j=negativePair k ↔ negativePair j=k := by
      constructor
      · rintro rfl
        exact negativePair_involutive k
      · intro h
        have hh := congrArg negativePair h
        exact (negativePair_involutive j).symm.trans hh
    simp only [Pi.single_apply,hiff]
  exact LinearMap.congr_fun he x

theorem normMatrixAction_negative_entry (i : Fin 4) (t : K) (j k : PairIndex) :
    normMatrixAction K (foldedRoot K true i t) j k=
      normMatrixAction K (foldedRoot K false i t) (negativePair j) (negativePair k) := by
  rw [normMatrixAction_entry,normMatrixAction_entry]
  have h := norm_positive_intertwines K i t (normBasis K (negativePair k))
  rw [normOpposition_normBasis,negativePair_involutive] at h
  have hc := congrArg (fun x : characteristicNormImage K=>normCoordinateEquiv K x j) h
  dsimp only at hc
  rw [normOpposition_coordinates] at hc
  exact hc.symm

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixNegativeAction
