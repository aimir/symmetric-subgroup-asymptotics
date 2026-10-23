import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionMatching
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOuterCovariance

/-! Negative simple-root covariance transported through the SAME actual
integral opposition on norm and quotient. The four final identities have
no covariance premises and use the already checked positive identities.
An original F4 exceptional automorphism remains a separate frontier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientNegativeCovariance
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoFixedQuotient
open CFSGFFourE6CharacteristicTwoQuotientAction CFSGFFourE6CharacteristicTwoOpposition
open CFSGFFourE6NormQuotientSelectedCovariance CFSGFFourE6NormQuotientOuterCovariance
open CFSGFFourE6NormQuotientOppositionMatching

private theorem negative_of_positive (K:Type) [Field K] [CharP K 2]
    (i j:Fin 4) (t s:K)
    (hp:∀x:characteristicFixedQuotient K,
      quotientToNorm K (quotientAction K (foldedRoot K false i t) x)=
        normAction K (foldedRoot K false j s) (quotientToNorm K x))
    (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K true i t) x)=
      normAction K (foldedRoot K true j s) (quotientToNorm K x) := by
  obtain ⟨y,rfl⟩:=(quotientOpposition K).surjective x
  calc
    quotientToNorm K (quotientAction K (foldedRoot K true i t) (quotientOpposition K y))=
        quotientToNorm K (quotientOpposition K (quotientAction K (foldedRoot K false i t) y)) :=
      congrArg (quotientToNorm K) (quotient_positive_intertwines K i t y).symm
    _=normOpposition K (quotientToNorm K (quotientAction K (foldedRoot K false i t) y)) :=
      quotientToNorm_opposition K _
    _=normOpposition K (normAction K (foldedRoot K false j s) (quotientToNorm K y)) :=
      congrArg (normOpposition K) (hp y)
    _=normAction K (foldedRoot K true j s) (normOpposition K (quotientToNorm K y)) :=
      norm_positive_intertwines K j s _
    _=normAction K (foldedRoot K true j s) (quotientToNorm K (quotientOpposition K y)) :=
      congrArg (normAction K (foldedRoot K true j s)) (quotientToNorm_opposition K y).symm

theorem negative_short_zero_covariance (K:Type) [Field K] [CharP K 2]
    (t:K) (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K true 0 t) x)=
      normAction K (foldedRoot K true 3 (t^2)) (quotientToNorm K x) :=
  negative_of_positive K 0 3 t (t^2) (outer_short_covariance K t) x

theorem negative_short_one_covariance (K:Type) [Field K] [CharP K 2]
    (t:K) (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K true 1 t) x)=
      normAction K (foldedRoot K true 2 (t^2)) (quotientToNorm K x) :=
  negative_of_positive K 1 2 t (t^2) (selected_short_covariance K t) x

theorem negative_long_two_covariance (K:Type) [Field K] [CharP K 2]
    (t:K) (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K true 2 t) x)=
      normAction K (foldedRoot K true 1 t) (quotientToNorm K x) :=
  negative_of_positive K 2 1 t t (selected_long_covariance K t) x

theorem negative_long_three_covariance (K:Type) [Field K] [CharP K 2]
    (t:K) (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K true 3 t) x)=
      normAction K (foldedRoot K true 0 t) (quotientToNorm K x) :=
  negative_of_positive K 3 0 t t (outer_long_covariance K t) x

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientNegativeCovariance
