import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylWordEquality
import SymmetricSubgroupAsymptotics.CFSGFFourMiddleWeylWordLists
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleParameterHoms

/-! The complete faithful norm26 certificate yields a constant
three-factor identity in the same original ReeF4 ambient Model.
The two positive factors and the conjugated middle factor remain literal
fixedMiddleWord values; no unrelated rank-one representation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWeylConstantWord
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalMiddleParameterHoms
open CFSGFFourMiddleWeylWordLists CFSGFFourOriginalMiddleWeylColumnAction
open CFSGFFourOriginalMiddleWeylWordEquality CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourFieldParameters CFSGReeFFourMiddleFixedWords
local notation "A" => CartanMatrix.F₄

private def oneRoot (K : Type) [_root_.Field K] (a : Bool×Fin 4) : Model A K :=
  modelRoot A K a.1 a.2 1

private theorem oneRoot_inv (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (a : Bool×Fin 4) : (oneRoot K a)⁻¹=oneRoot K a := by
  apply inv_eq_of_mul_eq_one_right
  change modelRoot A K a.1 a.2 1*modelRoot A K a.1 a.2 1=1
  rw [←source_root_add,CharTwo.add_self_eq_zero,source_root_zero]

private theorem middleValue_oneRoot (m : ℕ) :
    middleValue (oneRoot (Field m))=middleRelativeWeyl m := by
  simp only [middleValue,oneRoot,middleRelativeWeyl,weyl,CharTwo.neg_eq]
private theorem longValue_oneRoot (m : ℕ) :
    longValue (oneRoot (Field m))=middleLong (Field m) 1 := by
  simp only [longValue,oneRoot,middleLong,weyl,CharTwo.neg_eq]
private theorem shortValue_oneRoot (m : ℕ) :
    shortValue (oneRoot (Field m))=middleShort (Field m) 1 := by
  simp only [shortValue,oneRoot,middleShort,weyl,CharTwo.neg_eq]

theorem fixedMiddleWord_zero_one (m : ℕ) :
    fixedMiddleWord m 0 1=middleLong (Field m) 1*middleShort (Field m) 1 := by
  simp only [fixedMiddleWord,middleWord,map_zero,map_one,zero_pow (by decide : 2≠0),
    zero_mul,add_zero,source_root_zero,one_mul]

theorem fixedMiddleWord_one_zero (m : ℕ) :
    fixedMiddleWord m 1 0=modelRoot A (Field m) false 1 1*
      modelRoot A (Field m) false 2 1*middleLong (Field m) 1 := by
  have hzero : middleShort (Field m) 0=1 := (middleShortHom (Field m)).map_one
  simp only [fixedMiddleWord,middleWord,map_zero,map_one,one_pow,one_mul,zero_add,hzero,mul_one]

theorem fixedMiddleWord_one_one (m : ℕ) :
    fixedMiddleWord m 1 1=modelRoot A (Field m) false 1 1*
      modelRoot A (Field m) false 2 1*middleShort (Field m) 1 := by
  have hzero : middleLong (Field m) 0=1 := (middleLongHom (Field m)).map_one
  simp only [fixedMiddleWord,middleWord,map_one,one_pow,one_mul,
    CharTwo.add_self_eq_zero,hzero,mul_one]

theorem originalLeftWord_middle (m : ℕ) :
    originalLeftWord (Field m)=middleRelativeWeyl m := by
  have h := left_word_value (oneRoot (Field m))
  change originalLeftWord (Field m)=middleValue (oneRoot (Field m)) at h
  exact h.trans (middleValue_oneRoot m)

theorem originalRightWord_middle_factors (m : ℕ) :
    originalRightWord (Field m)=fixedMiddleWord m 0 1*
      (middleRelativeWeyl m*fixedMiddleWord m 1 0*(middleRelativeWeyl m)⁻¹)*
        fixedMiddleWord m 1 1 := by
  have h := right_word_value (oneRoot (Field m)) (oneRoot_inv (Field m))
  change originalRightWord (Field m)=_ at h
  rw [middleValue_oneRoot,longValue_oneRoot,shortValue_oneRoot] at h
  rw [fixedMiddleWord_zero_one,fixedMiddleWord_one_zero,fixedMiddleWord_one_one]
  simpa only [oneRoot] using h

theorem middleRelativeWeyl_constant_factors (m : ℕ) :
    middleRelativeWeyl m=fixedMiddleWord m 0 1*
      (middleRelativeWeyl m*fixedMiddleWord m 1 0*(middleRelativeWeyl m)⁻¹)*
        fixedMiddleWord m 1 1 :=
  (originalLeftWord_middle m).symm.trans
    ((original_middle_word_equality (Field m)).trans (originalRightWord_middle_factors m))

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWeylConstantWord
