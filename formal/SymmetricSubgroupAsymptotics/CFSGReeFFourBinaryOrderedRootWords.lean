import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveOrderedParameters
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterWeylMatrix
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleWeylMatrix

/-! Actual constant-root words for every ordered positive parameter.
The inverse prefix is the REVERSED root list. This is an original-group
identity, not a conclusion from equality of norm matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedRootWords
open CFSGFFourNormPrimeFieldWords CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourInversionPeelingWords CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOuterThreeWord CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourSimpleInversionBlocks CFSGReeFFourBinaryPositiveOrderedParameters
open CFSGOpposedPeelingOrderedParameters CFSGOpposedSubgroupPeelingChain
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalMiddleParameterHoms

private def weylLetters (i : Fin 4) : List Letter := [(false,i),(true,i),(false,i)]

private theorem weyl_letters_value (K : Type) [_root_.Field K]
    [Finite K] [CharP K 2] (i : Fin 4) :
    wordValue K (weylLetters i)=weyl K i := by
  simp only [weylLetters,wordValue,weyl,CharTwo.neg_eq,List.map_cons,
    List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc]

theorem outer_weyl_letters_value (m : ℕ) :
    wordValue (Field m) CFSGReeFFourBinarySeedOuterWeylMatrix.letters=
      outerRelativeWeyl m := by
  have hs : CFSGReeFFourBinarySeedOuterWeylMatrix.letters=
      weylLetters 0++weylLetters 3 := rfl
  rw [hs,wordValue_append,weyl_letters_value,weyl_letters_value]
  rfl

theorem middle_weyl_letters_value (m : ℕ) :
    wordValue (Field m) CFSGReeFFourBinarySeedMiddleWeylMatrix.letters=
      middleRelativeWeyl m := by
  have hs : CFSGReeFFourBinarySeedMiddleWeylMatrix.letters=
      ((weylLetters 1++weylLetters 2)++weylLetters 1)++weylLetters 2 := rfl
  simp only [hs,wordValue_append,weyl_letters_value]
  rfl

private theorem root_one_inv (K : Type) [_root_.Field K]
    [Finite K] [CharP K 2] (x : Letter) :
    (modelRoot CartanMatrix.F₄ K x.1 x.2 1)⁻¹=
      modelRoot CartanMatrix.F₄ K x.1 x.2 1 := by
  apply inv_eq_of_mul_eq_one_right
  rw [←source_root_add,CharTwo.add_self_eq_zero,source_root_zero]

theorem reversed_letters_value (K : Type) [_root_.Field K]
    [Finite K] [CharP K 2] (s : List Letter) :
    wordValue K s.reverse=(wordValue K s)⁻¹ := by
  induction s with
  | nil => simp only [wordValue,List.reverse_nil,List.map_nil,List.prod_nil,inv_one]
  | cons x s ih =>
    rw [List.reverse_cons,wordValue_append,ih]
    simp only [wordValue,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      mul_one,mul_inv_rev,root_one_inv]

theorem repeated_letters_value (K : Type) [_root_.Field K]
    (s : List Letter) (n : ℕ) :
    wordValue K ((List.replicate n s).flatten)=(wordValue K s)^n := by
  induction n with
  | zero => simp only [List.replicate_zero,List.flatten_nil,wordValue,
      List.map_nil,List.prod_nil,pow_zero]
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,wordValue_append,ih,pow_succ']

def stepLetters (n : ℕ) : List Letter :=
  if n%2=0 then CFSGReeFFourBinarySeedMiddleWeylMatrix.letters
  else CFSGReeFFourBinarySeedOuterWeylMatrix.letters

def baseLetters (n : ℕ) : List Letter :=
  if n%2=0 then fourCycleLetters else outerLetters

def baseElement (m n : ℕ) : originalModelFixed m :=
  if n%2=0 then fourCycle m else outerInvolution m

theorem step_letters_value (m n : ℕ) :
    wordValue (Field m) (stepLetters n)=(step m true n).val := by
  have hs : (step m true n).val=
      if axis true n then middleRelativeWeyl m else outerRelativeWeyl m :=
    single_paired_word_val m (axis true n)
  rw [hs]
  by_cases hn : n%2=0
  · simpa [stepLetters,axis,hn] using
      middle_weyl_letters_value m
  · simpa [stepLetters,axis,hn] using
      outer_weyl_letters_value m

theorem base_letters_value (m n : ℕ) :
    wordValue (Field m) (baseLetters n)=(baseElement m n).val := by
  by_cases hn : n%2=0
  · simpa only [baseLetters,baseElement,hn,if_true] using fourCycleLetters_value m
  · simpa only [baseLetters,baseElement,hn,if_false] using outerLetters_value m

def prefixLetters : ℕ → List Letter
  | 0 => []
  | n+1 => stepLetters n++prefixLetters n

theorem prefix_letters_value (m n : ℕ) :
    wordValue (Field m) (prefixLetters n)=(wordPrefix (step m true) n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixLetters,wordValue_append,step_letters_value,ih]
    rfl

def orderedLetters (a : ℕ → ℕ) : ℕ → List Letter
  | 0 => []
  | n+1 => (prefixLetters n).reverse++
      (List.replicate (a n) (baseLetters n)).flatten++
      prefixLetters n++orderedLetters a n

theorem ordered_letters_value (m : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    wordValue (Field m) (orderedLetters a n)=
      (orderedProduct (step m true) n
        (fun j => (baseElement m j.val)^(a j.val))).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [orderedLetters,wordValue_append,reversed_letters_value,
      repeated_letters_value,prefix_letters_value,base_letters_value,ih]
    simp only [orderedProduct,Fin.val_last,Fin.val_castSucc,
      Subgroup.coe_mul,Subgroup.coe_inv,Subgroup.coe_pow,mul_assoc]

theorem baseElement_eq_blockBase (j : Fin 8) : baseElement 0 j.val=blockBase j := by
  simp [baseElement,blockBase,axis]

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedRootWords
