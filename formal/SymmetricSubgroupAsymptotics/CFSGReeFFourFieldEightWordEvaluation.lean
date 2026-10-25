import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightWordTemplates
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightFixedSelectedWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylInvolutions
import Mathlib.Tactic.Group

/-! The selected70 signed simple roots evaluate to the same actual
original fixed-group element. Zero parameters and reversed Weyl shells
are justified in the actual original Model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightWordEvaluation
open CFSGReeFFourFieldEightWordTemplates CFSGReeFFourFieldEightFixedSelectedWord
open CFSGReeFFourFieldEightCertificateField CFSGReeFFourFieldParameters
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourOriginalFoldedEquivalence CFSGFFourOriginalMiddleWords
open CFSGReeFFourOuterFixedRoot CFSGReeFFourMiddleFixedWords
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativeWeylInvolutions

private instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

private theorem root_zero (neg : Bool) (i : Fin 4) :
    modelRoot CartanMatrix.F₄ (Field 1) neg i 0 = 1 := by
  apply (modelEquivFolded (Field 1)).injective
  rw [modelEquivFolded_root, map_one]
  apply Subtype.ext
  exact canonicalRoot_zero CFSGFFourSerreMatrices.realizationData (Field 1) neg i

def wordValue (s : List Letter) : Model CartanMatrix.F₄ (Field 1) :=
  (s.map (fun x => modelRoot CartanMatrix.F₄ (Field 1) x.1 x.2.1
    (fieldEquiv x.2.2))).prod

theorem wordValue_append (s t : List Letter) :
    wordValue (s ++ t) = wordValue s * wordValue t := by
  simp only [wordValue, List.map_append, List.prod_append]

theorem rootLetters_value (neg : Bool) (i : Fin 4) (t : Element) :
    wordValue (rootLetters neg i t) =
      modelRoot CartanMatrix.F₄ (Field 1) neg i (fieldEquiv t) := by
  by_cases ht : t = 0
  · subst t
    simp [rootLetters, wordValue, root_zero]
  · simp only [rootLetters, if_neg ht, wordValue, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem weylLetters_value (i : Fin 4) :
    wordValue (weylLetters i) = weyl (Field 1) i := by
  simp only [weylLetters, wordValue_append, rootLetters_value, map_one,
    weyl, CharTwo.neg_eq]

theorem middleLetters_value (b c : Element) :
    wordValue (middleLetters b c) = fixedMiddleWord 1 (fieldEquiv b) (fieldEquiv c) := by
  simp only [middleLetters, wordValue_append, rootLetters_value,
    weylLetters_reverse, weylLetters_value, map_add, map_mul, map_pow,
    fixedMiddleWord, middleWord, middleLong, middleShort, original_weyl_inv,
    alpha_apply]
  norm_num only [Nat.reduceAdd, Nat.reducePow]
  group

theorem blockLetters_value (a b c : Element) :
    wordValue (blockLetters a b c) = (selectedBlock a b c).val := by
  simp only [blockLetters, wordValue_append, rootLetters_value,
    middleLetters_value, weylLetters_value, map_pow, selectedBlock_val,
    outerWord, outerRelativeWeyl, middleRelativeWeyl, alpha_apply]
  norm_num only [Nat.reduceAdd, Nat.reducePow]
  group

theorem selectedLetters_value : wordValue selectedLetters = selectedElement.val := by
  rw [selectedLetters_eq, wordValue_append, blockLetters_value, blockLetters_value]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightWordEvaluation
