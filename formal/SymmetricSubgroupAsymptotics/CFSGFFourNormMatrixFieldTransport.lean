import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixNegativeAction

/-! Signed-simple matrices of the same norm26 action commute with an
actual coefficient-field homomorphism. No group recognition or new
matrix certificate is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormMatrixFieldTransport
open CFSGFFourE6NormMatrixAction CFSGFFourE6NormMatrixNegativeAction
open CFSGFFourE6CharacteristicTwoNormImage
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormQuotientCoordinateRootActions
open CFSGFFourE6NormQuotientOppositionLabels
variable {K L : Type} [Field K] [CharP K 2] [Field L] [CharP L 2]
private instance : Fintype PairIndex := by unfold PairIndex; infer_instance

theorem map_positive (e : K →+* L) (i : Fin 4) (t : K) :
    (normMatrixAction K (foldedRoot K false i t)).map e =
      normMatrixAction L (foldedRoot L false i (e t)) := by
  classical
  ext j k
  simp only [Matrix.map_apply,normMatrixAction_positive_entry,
    map_add,map_mul,map_pow,map_intCast]
  by_cases h : j = k <;> simp [Pi.single_apply,h]

theorem map_signed (e : K →+* L) (neg : Bool) (i : Fin 4) (t : K) :
    (normMatrixAction K (foldedRoot K neg i t)).map e =
      normMatrixAction L (foldedRoot L neg i (e t)) := by
  cases neg with
  | false => exact map_positive e i t
  | true =>
    ext j k
    change e (normMatrixAction K (foldedRoot K true i t) j k) =
      normMatrixAction L (foldedRoot L true i (e t)) j k
    rw [normMatrixAction_negative_entry,normMatrixAction_negative_entry]
    exact congrArg (fun M : Matrix PairIndex PairIndex L =>
      M (negativePair j) (negativePair k)) (map_positive e i t)

end SymmetricSubgroupAsymptotics.CFSGFFourNormMatrixFieldTransport
