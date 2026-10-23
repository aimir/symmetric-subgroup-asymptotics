import SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleCoefficientPilot
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOuterCoefficients
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientNegativeCovariance

/-! Injectivity of each literal signed simple parameter in the actual
norm26 action. A coefficient-one linear entry recovers the parameter;
negative signs are transported by actual integral opposition. No full-U
or whole-group faithfulness is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleParameters
open CFSGFFourSerreMatrices CFSGTwistedE6GeckDiagramCovariance
open CFSGFFourE6NormSimpleCoefficientPilot CFSGFFourE6NormQuotientCoefficientPilot
open CFSGFFourE6NormQuotientOuterCoefficientPilot CFSGFFourE6NormQuotientStepEntries
open CFSGFFourE6NormQuotientSelectedCoefficients CFSGFFourE6NormPairRepresentatives
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6NormQuotientCoordinateRootActions CFSGFFourE6CharacteristicTwoOpposition
open CFSGSerreQuadraticMatrix

private theorem first_entry (i:Fin 4) (r s:Index) :
    integerE i r s=firstEntry i (eraseGeck r) (eraseGeck s) := by
  fin_cases i
  · change (e6EZ 0+e6EZ 5) r s=outerShortFirst (eraseGeck r) (eraseGeck s)
    rw [Matrix.add_apply,e6EZ_entry,e6EZ_entry]
    rfl
  · change (e6EZ 2+e6EZ 4) r s=shortFirst (eraseGeck r) (eraseGeck s)
    rw [Matrix.add_apply,e6EZ_entry,e6EZ_entry]
    rfl
  · exact e6EZ_entry 3 r s
  · exact e6EZ_entry 1 r s

private theorem quadratic_entry (i:Fin 4) (r s:Index) :
    positiveSecondZ i r s=quadraticEntry i (eraseGeck r) (eraseGeck s) := by
  fin_cases i
  · change (e6SecondZ 0+e6SecondZ 5+e6EZ 0*e6EZ 5) r s=outerShortSecond (eraseGeck r) (eraseGeck s)
    rw [Matrix.add_apply,Matrix.add_apply,e6SecondZ_entry,e6SecondZ_entry,
      CFSGFFourE6NormQuotientOuterProductEntry.e6EZ_orthogonal_product_entry]
    rfl
  · change (e6SecondZ 2+e6SecondZ 4+e6EZ 2*e6EZ 4) r s=shortSecond (eraseGeck r) (eraseGeck s)
    rw [Matrix.add_apply,Matrix.add_apply,e6SecondZ_entry,e6SecondZ_entry,
      CFSGFFourE6NormQuotientProductEntry.e6EZ_orthogonal_product_entry]
    rfl
  · exact e6SecondZ_entry 3 r s
  · exact e6SecondZ_entry 1 r s

private theorem norm_coefficient_eq (M:IntMat) (T:RawIndex→RawIndex→ℤ)
    (hM:∀r s,M r s=T (eraseGeck r) (eraseGeck s)) (j k:PairIndex) :
    actualNormCoefficient M j k=normCoefficient T j k := by
  simp only [actualNormCoefficient,hM,eraseGeck_selectedRepresentative,
    eraseGeck_partnerRepresentative,normCoefficient]

theorem first_norm_coefficient (i:Fin 4) (j k:PairIndex) :
    actualNormCoefficient (integerE i) j k=normCoefficient (firstEntry i) j k :=
  norm_coefficient_eq _ _ (first_entry i) j k

theorem quadratic_norm_coefficient (i:Fin 4) (j k:PairIndex) :
    actualNormCoefficient (positiveSecondZ i) j k=normCoefficient (quadraticEntry i) j k :=
  norm_coefficient_eq _ _ (quadratic_entry i) j k

theorem exists_cast_linear_witness (K:Type) [Field K] [CharP K 2] (i:Fin 4) :
    ∃j k:PairIndex,(actualNormCoefficient (integerE i) j k:K)=1 ∧
      (actualNormCoefficient (positiveSecondZ i) j k:K)=0 := by
  obtain ⟨j,k,hE,hD⟩:=exists_norm_linear_witness i
  refine ⟨j,k,?_,?_⟩
  · calc
      (actualNormCoefficient (integerE i) j k:K)=
          ((actualNormCoefficient (integerE i) j k%2:ℤ):K) := CharP.intCast_eq_intCast_mod K 2
      _=1 := by rw [first_norm_coefficient,hE,Int.cast_one]
  · calc
      (actualNormCoefficient (positiveSecondZ i) j k:K)=
          ((actualNormCoefficient (positiveSecondZ i) j k%2:ℤ):K) := CharP.intCast_eq_intCast_mod K 2
      _=0 := by rw [quadratic_norm_coefficient,hD,Int.cast_zero]

theorem norm_positive_parameter_injective (K:Type) [Field K] [CharP K 2] (i:Fin 4) :
    Function.Injective (fun t:K=>normAction K (foldedRoot K false i t)) := by
  obtain ⟨j,k,hE,hD⟩:=exists_cast_linear_witness K i
  intro t u he
  have h:=congrArg (fun f:characteristicNormImage K≃ₗ[K]characteristicNormImage K=>
    normCoordinateEquiv K (f (normBasis K k)) j) he
  simp only [normAction_coordinates_basis,hE,hD,mul_one,mul_zero,add_zero] at h
  exact add_left_cancel h

theorem norm_negative_parameter_injective (K:Type) [Field K] [CharP K 2] (i:Fin 4) :
    Function.Injective (fun t:K=>normAction K (foldedRoot K true i t)) := by
  intro t u he
  dsimp only at he
  apply norm_positive_parameter_injective K i
  apply LinearEquiv.ext
  intro x
  apply (normOpposition K).injective
  rw [norm_positive_intertwines,norm_positive_intertwines,he]

theorem norm_simple_parameter_injective (K:Type) [Field K] [CharP K 2] (neg:Bool) (i:Fin 4) :
    Function.Injective (fun t:K=>normAction K (foldedRoot K neg i t)) := by
  cases neg
  · exact norm_positive_parameter_injective K i
  · exact norm_negative_parameter_injective K i

theorem norm_simple_zero (K:Type) [Field K] (neg:Bool) (i:Fin 4) :
    normAction K (foldedRoot K neg i 0)=1 := by
  have hz:foldedRoot K neg i 0=(1:canonicalElementaryGroup realizationData K) := by
    apply Subtype.ext
    change canonicalRoot realizationData K neg i 0=1
    exact canonicalRoot_zero realizationData K neg i
  rw [hz,map_one]

theorem norm_simple_one_ne_one (K:Type) [Field K] [CharP K 2] (neg:Bool) (i:Fin 4) :
    normAction K (foldedRoot K neg i 1)≠1 := by
  intro he
  have ht:(1:K)=0:=norm_simple_parameter_injective K neg i
    (he.trans (norm_simple_zero K neg i).symm)
  exact one_ne_zero ht

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleParameters
