import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleScalarColumnAction
import SymmetricSubgroupAsymptotics.CFSGFFourMiddleScalarWordLists
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleScalarResidual

/-! The single tested variable column belongs to the literal original
middle residual. The bridge uses prescribed original root parameters,
not recognition of a separate rank-one action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleScalarColumn
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourOriginalFoldedEquivalence CFSGFFourE6MiddleScalarColumnAction
open CFSGFFourE6MiddleScalarColumnCertificate CFSGFFourE6MiddleScalarPolynomialData
open CFSGFFourMiddleScalarWordLists CFSGFFourMiddleWeylWordLists
open CFSGFFourE6MiddleWeylColumnAction CFSGFFourE6MiddleWeylCoordinateSteps
open CFSGFFourE6CharacteristicTwoNormImage CFSGSparseBivariateListEvaluation
open CFSGReeFFourFieldParameters CFSGReeFFourMiddleScalarResidual
open CFSGReeFFourMiddleWeylConstantWord CFSGReeFFourMiddleFixedWords
open CFSGReeFFourOriginalMiddleWeylScalarWord CFSGReeFFourRelativeSimpleWeyl
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalMiddleParameterHoms
open CFSGReeFFourOppositeGenerationAssembly

private def tokenRoot (K : Type) [Field K] [Finite K] [CharP K 2]
    (c d : K) (a : Action) : Model CartanMatrix.F₄ K :=
  modelRoot CartanMatrix.F₄ K a.1.1 a.1.2 (monomialValue c d a.2)

private theorem tokenRoot_inv (K : Type) [Field K] [Finite K] [CharP K 2]
    (c d : K) (a : Action) : (tokenRoot K c d a)⁻¹=tokenRoot K c d a := by
  apply inv_eq_of_mul_eq_one_right
  change modelRoot CartanMatrix.F₄ K a.1.1 a.1.2 (monomialValue c d a.2)*
    modelRoot CartanMatrix.F₄ K a.1.1 a.1.2 (monomialValue c d a.2)=1
  rw [←source_root_add,CharTwo.add_self_eq_zero,source_root_zero]

def originalTestedWord (K : Type) [Field K] [Finite K] [CharP K 2] (c d : K) :
    Model CartanMatrix.F₄ K := actionWord (fun i : Fin 68=>tokenRoot K c d (actions i))

theorem modelEquivFolded_testedWord (K : Type) [Field K] [Finite K] [CharP K 2] (c d : K) :
    modelEquivFolded K (originalTestedWord K c d)=testedWord K c d := by
  simp only [originalTestedWord,testedWord,actionWord,map_list_prod,List.map_reverse,List.map_ofFn]
  apply congrArg (fun f : Fin 68→canonicalElementaryGroup CFSGFFourSerreMatrices.realizationData K=>
    (List.ofFn f).reverse.prod)
  funext i
  change modelEquivFolded K (modelRoot CartanMatrix.F₄ K (actions i).1.1 (actions i).1.2
    (monomialValue c d (actions i).2))=foldedRoot K (actions i).1.1 (actions i).1.2
      (monomialValue c d (actions i).2)
  exact modelEquivFolded_root K _ _ _

private theorem middleValue_tokenRoot (m : ℕ) (c d : Field m) :
    middleValue (rootOne (tokenRoot (Field m) c d))=middleRelativeWeyl m := by
  simp only [middleValue,rootOne,tokenRoot,monomialValue,pow_zero,one_mul,middleRelativeWeyl,weyl,CharTwo.neg_eq]
private theorem longValue_tokenRoot (m : ℕ) (c d : Field m) :
    longValue (rootOne (tokenRoot (Field m) c d))=middleLong (Field m) 1 := by
  simp only [longValue,rootOne,tokenRoot,monomialValue,pow_zero,one_mul,middleLong,weyl,CharTwo.neg_eq]
private theorem shortValue_tokenRoot (m : ℕ) (c d : Field m) :
    shortValue (rootOne (tokenRoot (Field m) c d))=middleShort (Field m) 1 := by
  simp only [shortValue,rootOne,tokenRoot,monomialValue,pow_zero,one_mul,middleShort,weyl,CharTwo.neg_eq]
private theorem fixedMiddleWord_c_zero (m : ℕ) (c : Field m) :
    fixedMiddleWord m c 0=modelRoot CartanMatrix.F₄ (Field m) false 1 c*
      modelRoot CartanMatrix.F₄ (Field m) false 2 (alpha m c)*middleLong (Field m) (c^2*alpha m c) := by
  have hz : middleShort (Field m) 0=1 := (middleShortHom (Field m)).map_one
  simp only [fixedMiddleWord,middleWord,map_zero,zero_add,hz,mul_one]

theorem original_testedWord_eq_middleResidual (m : ℕ) (c : Field m) :
    originalTestedWord (Field m) c (alpha m c)=(middleScalarResidual m c).val := by
  have he := residual_word_value (tokenRoot (Field m) c (alpha m c))
    (tokenRoot_inv (Field m) c (alpha m c))
  change originalTestedWord (Field m) c (alpha m c)=_ at he
  rw [residualValue,middleValue_tokenRoot,longValue_tokenRoot,shortValue_tokenRoot] at he
  change originalTestedWord (Field m) c (alpha m c)=_
  rw [he]
  change _=(fixedMiddleWord m 0 1*
    (middleRelativeWeyl m*fixedMiddleWord m c 0*(middleRelativeWeyl m)⁻¹)*fixedMiddleWord m 1 1)*
      (middleRelativeWeyl m)⁻¹
  rw [fixedMiddleWord_zero_one,fixedMiddleWord_one_one,fixedMiddleWord_c_zero]
  simp only [rootOne,tokenRoot,monomialValue,pow_zero,pow_one,one_mul,mul_one]
  simp only [weyl,CharTwo.neg_eq,middleLong]
  group

theorem original_middleResidual_entry (m : ℕ) (c : Field m) :
    matrixAction (Field m)
      (modelEquivFolded (Field m) (middleScalarResidual m c).val) 13 0=c+c^2 := by
  rw [←original_testedWord_eq_middleResidual,modelEquivFolded_testedWord]
  exact testedWord_entry_thirteen_zero (Field m) c (alpha m c)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleScalarColumn
