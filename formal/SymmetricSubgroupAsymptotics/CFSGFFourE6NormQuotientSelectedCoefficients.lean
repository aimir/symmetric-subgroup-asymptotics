import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientProductEntry
import Mathlib.Algebra.CharP.Basic

/-! The selected mod-two arithmetic identities hold for the literal
integral folded Geck operators, hence in every characteristic-two
coefficient ring. The root action comparison is a later linear step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientSelectedCoefficients
open CFSGFFourSerreMatrices CFSGTwistedE6GeckDiagramCovariance
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives
open CFSGFFourE6NormQuotientRootMatching CFSGFFourE6NormQuotientCoefficientPilot
open CFSGFFourE6NormQuotientStepEntries CFSGFFourE6NormQuotientProductEntry

def actualNormCoefficient (M:IntMat) (j k:PairIndex) : ℤ :=
  M (selectedRepresentative j) (selectedRepresentative k)+
    M (selectedRepresentative j) (diagramIndex (selectedRepresentative k))

def actualQuotientCoefficient (M:IntMat) (j k:PairIndex) : ℤ :=
  M (fixedRepresentative (basisIndexDual j)) (fixedRepresentative (basisIndexDual k))

private theorem norm_coefficient_eq (M:IntMat) (T:RawIndex→RawIndex→ℤ)
    (hM:∀r s,M r s=T (eraseGeck r) (eraseGeck s)) (j k:PairIndex) :
    actualNormCoefficient M j k=normCoefficient T j k := by
  simp only [actualNormCoefficient,hM,eraseGeck_selectedRepresentative,
    eraseGeck_partnerRepresentative,normCoefficient]

private theorem quotient_coefficient_eq (M:IntMat) (T:RawIndex→RawIndex→ℤ)
    (hM:∀r s,M r s=T (eraseGeck r) (eraseGeck s)) (j k:PairIndex) :
    actualQuotientCoefficient M j k=quotientCoefficient T j k := by
  simp only [actualQuotientCoefficient,hM,eraseGeck_fixedRepresentative,quotientCoefficient]

private theorem short_first_entry (r s:Index) :
    integerE 1 r s=shortFirst (eraseGeck r) (eraseGeck s) := by
  change (e6EZ 2+e6EZ 4) r s=_
  rw [Matrix.add_apply,e6EZ_entry,e6EZ_entry]
  rfl

private theorem long_first_entry (r s:Index) :
    integerE 2 r s=longFirst (eraseGeck r) (eraseGeck s) := e6EZ_entry 3 r s

private theorem short_second_entry (r s:Index) :
    positiveSecondZ 1 r s=shortSecond (eraseGeck r) (eraseGeck s) := by
  change (e6SecondZ 2+e6SecondZ 4+e6EZ 2*e6EZ 4) r s=_
  rw [Matrix.add_apply,Matrix.add_apply,e6SecondZ_entry,e6SecondZ_entry,e6EZ_orthogonal_product_entry]
  rfl

private theorem long_second_entry (r s:Index) :
    positiveSecondZ 2 r s=longSecond (eraseGeck r) (eraseGeck s) := e6SecondZ_entry 3 r s

theorem actual_short_quotient_linear_zero (j k:PairIndex) :
    actualQuotientCoefficient (integerE 1) j k%2=0 := by
  rw [quotient_coefficient_eq _ _ short_first_entry]
  exact short_quotient_linear_zero j k

theorem actual_short_quotient_quadratic (j k:PairIndex) :
    actualQuotientCoefficient (positiveSecondZ 1) j k%2=
      actualNormCoefficient (integerE 2) j k%2 := by
  rw [quotient_coefficient_eq _ _ short_second_entry,norm_coefficient_eq _ _ long_first_entry]
  exact short_quotient_quadratic_eq_long_norm_linear j k

theorem actual_long_norm_quadratic_zero (j k:PairIndex) :
    actualNormCoefficient (positiveSecondZ 2) j k%2=0 := by
  rw [norm_coefficient_eq _ _ long_second_entry]
  exact long_norm_quadratic_zero j k

theorem actual_long_quotient_linear (j k:PairIndex) :
    actualQuotientCoefficient (integerE 2) j k%2=actualNormCoefficient (integerE 1) j k%2 := by
  rw [quotient_coefficient_eq _ _ long_first_entry,norm_coefficient_eq _ _ short_first_entry]
  exact long_quotient_linear_eq_short_norm_linear j k

theorem actual_long_quotient_quadratic (j k:PairIndex) :
    actualQuotientCoefficient (positiveSecondZ 2) j k%2=
      actualNormCoefficient (positiveSecondZ 1) j k%2 := by
  rw [quotient_coefficient_eq _ _ long_second_entry,norm_coefficient_eq _ _ short_second_entry]
  exact long_quotient_quadratic_eq_short_norm_quadratic j k

private theorem cast_eq_of_mod_two (K:Type*) [CommRing K] [CharP K 2]
    (a b:ℤ) (he:a%2=b%2) : (a:K)=(b:K) := by
  calc
    (a:K)=((a%2:ℤ):K):=CharP.intCast_eq_intCast_mod K 2
    _=((b%2:ℤ):K):=congrArg (fun n:ℤ=>(n:K)) he
    _=(b:K):=(CharP.intCast_eq_intCast_mod K 2).symm

theorem cast_short_quotient_linear_zero (K:Type*) [CommRing K] [CharP K 2] (j k:PairIndex) :
    (actualQuotientCoefficient (integerE 1) j k:K)=0 := by
  simpa only [Int.cast_zero] using cast_eq_of_mod_two K _ 0 (actual_short_quotient_linear_zero j k)

theorem cast_short_quotient_quadratic (K:Type*) [CommRing K] [CharP K 2] (j k:PairIndex) :
    (actualQuotientCoefficient (positiveSecondZ 1) j k:K)=(actualNormCoefficient (integerE 2) j k:K) :=
  cast_eq_of_mod_two K _ _ (actual_short_quotient_quadratic j k)

theorem cast_long_norm_quadratic_zero (K:Type*) [CommRing K] [CharP K 2] (j k:PairIndex) :
    (actualNormCoefficient (positiveSecondZ 2) j k:K)=0 := by
  simpa only [Int.cast_zero] using cast_eq_of_mod_two K _ 0 (actual_long_norm_quadratic_zero j k)

theorem cast_long_quotient_linear (K:Type*) [CommRing K] [CharP K 2] (j k:PairIndex) :
    (actualQuotientCoefficient (integerE 2) j k:K)=(actualNormCoefficient (integerE 1) j k:K) :=
  cast_eq_of_mod_two K _ _ (actual_long_quotient_linear j k)

theorem cast_long_quotient_quadratic (K:Type*) [CommRing K] [CharP K 2] (j k:PairIndex) :
    (actualQuotientCoefficient (positiveSecondZ 2) j k:K)=(actualNormCoefficient (positiveSecondZ 1) j k:K) :=
  cast_eq_of_mod_two K _ _ (actual_long_quotient_quadratic j k)

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientSelectedCoefficients
