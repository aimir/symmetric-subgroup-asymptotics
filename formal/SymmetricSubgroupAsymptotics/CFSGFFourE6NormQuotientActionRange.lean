import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientNegativeCovariance
import SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange
import Mathlib.FieldTheory.Finite.Basic

/-! The two actual 26-dimensional actions have the same image after the
checked coordinate identification. Only the reverse inclusion needs a
finite field, through surjectivity of squaring in characteristic two.
This statement concerns the literal folded matrix group, without an
ordinary F4 simplicity or original-model correspondence premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientActionRange
open CFSGFFourSerreMatrices CFSGSerreQuadraticMatrix
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoFixedQuotient
open CFSGFFourE6CharacteristicTwoQuotientAction CFSGFFourE6NormQuotientSelectedCovariance
open CFSGFFourE6NormQuotientOuterCovariance CFSGFFourE6NormQuotientNegativeCovariance

def reversedNode (i:Fin 4) : Fin 4 := ⟨3-i.val,by omega⟩

def exceptionalParameter {K:Type} [Field K] (i:Fin 4) (t:K) : K :=
  if i.val<2 then t^2 else t

def quotientOnNorm (K:Type) [Field K] [CharP K 2] :
    canonicalElementaryGroup realizationData K→*
      (characteristicNormImage K≃ₗ[K]characteristicNormImage K) where
  toFun g := ((quotientToNorm K).symm.trans (quotientAction K g)).trans (quotientToNorm K)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change quotientToNorm K (quotientAction K 1 ((quotientToNorm K).symm x))=x
    rw [map_one]
    exact (quotientToNorm K).apply_symm_apply x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change quotientToNorm K (quotientAction K (g*h) ((quotientToNorm K).symm x))=
      quotientToNorm K (quotientAction K g
        ((quotientToNorm K).symm (quotientToNorm K
          (quotientAction K h ((quotientToNorm K).symm x)))))
    rw [LinearEquiv.symm_apply_apply,map_mul]
    rfl

theorem quotientOnNorm_apply (K:Type) [Field K] [CharP K 2]
    (g:canonicalElementaryGroup realizationData K) (x:characteristicNormImage K) :
    quotientOnNorm K g x=
      quotientToNorm K (quotientAction K g ((quotientToNorm K).symm x)) := rfl

theorem signed_root_covariance (K:Type) [Field K] [CharP K 2]
    (neg:Bool) (i:Fin 4) (t:K) (x:characteristicFixedQuotient K) :
    quotientToNorm K (quotientAction K (foldedRoot K neg i t) x)=
      normAction K (foldedRoot K neg (reversedNode i) (exceptionalParameter i t))
        (quotientToNorm K x) := by
  cases neg with
  | false=>
    fin_cases i
    · exact outer_short_covariance K t x
    · exact selected_short_covariance K t x
    · exact selected_long_covariance K t x
    · exact outer_long_covariance K t x
  | true=>
    fin_cases i
    · exact negative_short_zero_covariance K t x
    · exact negative_short_one_covariance K t x
    · exact negative_long_two_covariance K t x
    · exact negative_long_three_covariance K t x

theorem quotientOnNorm_root (K:Type) [Field K] [CharP K 2]
    (neg:Bool) (i:Fin 4) (t:K) :
    quotientOnNorm K (foldedRoot K neg i t)=
      normAction K (foldedRoot K neg (reversedNode i) (exceptionalParameter i t)) := by
  apply LinearEquiv.ext
  intro x
  rw [quotientOnNorm_apply,signed_root_covariance,LinearEquiv.apply_symm_apply]

theorem square_surjective (K:Type) [Field K] [Finite K] [CharP K 2] :
    Function.Surjective (fun t:K=>t^2) :=
  Finite.surjective_of_injective (frobenius_inj K 2)

theorem action_ranges_eq (K:Type) [Field K] [Finite K] [CharP K 2] :
    (quotientOnNorm K).range=(normAction K).range := by
  apply le_antisymm
  · apply CFSGGeneratedActionRange.range_le_of_generators
      (elementaryRootSet K (canonicalRoot realizationData K))
      (elementaryRootSet_generate K (canonicalRoot realizationData K))
      (quotientOnNorm K) (normAction K).range
    rintro g ⟨neg,i,t,rfl⟩
    exact ⟨foldedRoot K neg (reversedNode i) (exceptionalParameter i t),
      (quotientOnNorm_root K neg i t).symm⟩
  · apply CFSGGeneratedActionRange.range_le_of_generators
      (elementaryRootSet K (canonicalRoot realizationData K))
      (elementaryRootSet_generate K (canonicalRoot realizationData K))
      (normAction K) (quotientOnNorm K).range
    rintro g ⟨neg,i,t,rfl⟩
    fin_cases i
    · refine ⟨foldedRoot K neg 3 t,?_⟩
      exact quotientOnNorm_root K neg 3 t
    · refine ⟨foldedRoot K neg 2 t,?_⟩
      exact quotientOnNorm_root K neg 2 t
    · obtain ⟨s,hs⟩:=square_surjective K t
      dsimp only at hs
      refine ⟨foldedRoot K neg 1 s,?_⟩
      have he:=quotientOnNorm_root K neg 1 s
      change quotientOnNorm K (foldedRoot K neg 1 s)=normAction K (foldedRoot K neg 2 (s^2)) at he
      rw [hs] at he
      exact he
    · obtain ⟨s,hs⟩:=square_surjective K t
      dsimp only at hs
      refine ⟨foldedRoot K neg 0 s,?_⟩
      have he:=quotientOnNorm_root K neg 0 s
      change quotientOnNorm K (foldedRoot K neg 0 s)=normAction K (foldedRoot K neg 3 (s^2)) at he
      rw [hs] at he
      exact he

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientActionRange
