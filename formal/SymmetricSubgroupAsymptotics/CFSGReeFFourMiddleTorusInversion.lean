import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleTorusExponentCertificate
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeGenerationAssembly

/-! Actual middle Weyl inversion of the genuine fixed torus. The six
ambient torus coordinates are retained; literal Weyl conjugation and the
bounded cocharacter certificate prove the action. No middle generation,
ordinary F4 simplicity, or desired torus-action premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusInversion
open CFSGE6GeckMiddleTorusExponentCertificate CFSGE6GeckProductTorusWeylAction
open CFSGE6GeckProductTorus CFSGNormTwoGeckWeylWordDegree
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGReeFFourFieldParameters
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalProductTorus
open CFSGReeFFourFixedTorus CFSGReeFFourParameterizedTorusCovariance
open CFSGFFourE6ScalarTuple CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourOppositeGenerationAssembly CFSGReeFFourRelativeSimpleWeyl

private theorem scalarTuple_middle {G : Type*} [CommGroup G] (b c : G) :
    scalarTupleHom ![1,b,c,1]=middleTuple b c := by
  funext i
  fin_cases i <;> simp [scalarTupleHom,middleTuple,Pi.mulSingle_apply,Fin.ext_iff]

theorem raw_middle_torus_inversion (K : Type) [_root_.Field K] (b c : Kˣ) :
    wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
        [2,4,3,2,4,3]*rawProductTorus K (middleTuple b c)*
      (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
        [2,4,3,2,4,3])⁻¹=(rawProductTorus K (middleTuple b c))⁻¹ := by
  rw [word_product_torus,middle_tuple_inverted,map_inv]

theorem rawHom_fixedTorus_middle (m : ℕ) (b : (Field m)ˣ) :
    rawHom (Field m) (fixedTorus m 1 b).val=
      rawProductTorus (Field m) (middleTuple b (unitPower m 1 b)) := by
  have hU : unitPower m 0 (1 : (Field m)ˣ)=1 := by
    apply Units.ext
    rw [unitPower_val]
    simp
  have ht : CFSGReeFFourFixedTorus.fixedTorusTuple m 1 b=![1,b,unitPower m 1 b,1] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact hU
  rw [fixedTorus_val,rawHom_modelProductTorus]
  change rawProductTorus (Field m) (scalarTupleHom
    (CFSGReeFFourFixedTorus.fixedTorusTuple m 1 b))=_
  rw [ht,scalarTuple_middle]

theorem middle_fixed_torus_inversion (m : ℕ) (b : (Field m)ˣ) :
    fixedMiddleWeyl m*fixedTorus m 1 b*(fixedMiddleWeyl m)⁻¹=(fixedTorus m 1 b)⁻¹ := by
  apply Subtype.ext
  apply rawHom_injective (Field m)
  change rawHom (Field m) (middleRelativeWeyl m*(fixedTorus m 1 b).val*(middleRelativeWeyl m)⁻¹)=
    rawHom (Field m) ((fixedTorus m 1 b).val⁻¹)
  simp only [map_mul,map_inv,rawHom_middleRelativeWeyl,rawHom_fixedTorus_middle]
  exact raw_middle_torus_inversion (Field m) b (unitPower m 1 b)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusInversion
