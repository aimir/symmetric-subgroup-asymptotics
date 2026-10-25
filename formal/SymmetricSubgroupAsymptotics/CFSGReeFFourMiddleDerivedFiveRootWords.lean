import SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterDerivedPositive

/-! Exact constant-root lists for the derived order-five word and an actual
positive commutator. No commutation inequality or quotient order is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGFFourNormPrimeFieldWords CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalMiddleParameterHoms CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWeylConstantWord
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOuterFixedRoot CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourDerivedAmbientHom
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration

private def weylLetters (i : Fin 4) : List Letter := [(false,i),(true,i),(false,i)]
private def longLetters : List Letter := weylLetters 1 ++ [(false,2)] ++ (weylLetters 1).reverse
private def shortLetters : List Letter := weylLetters 2 ++ [(false,1)] ++ (weylLetters 2).reverse
private def middleWeylLetters : List Letter :=
  weylLetters 1 ++ weylLetters 2 ++ weylLetters 1 ++ weylLetters 2

def outerLetters : List Letter := [(false,0),(false,3)]
def fourCycleLetters : List Letter := [(false,1),(false,2)] ++ longLetters

def fiveLetters : List Letter := middleWeylLetters ++ longLetters ++ shortLetters

def positiveCommutatorLetters : List Letter :=
  outerLetters ++ fourCycleLetters ++ outerLetters.reverse ++ fourCycleLetters.reverse

private theorem oneRoot_inv (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (x : Letter) : (modelRoot CartanMatrix.F₄ K x.1 x.2 1)⁻¹ =
      modelRoot CartanMatrix.F₄ K x.1 x.2 1 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← source_root_add, CharTwo.add_self_eq_zero, source_root_zero]

private theorem wordValue_reverse (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (s : List Letter) : wordValue K s.reverse = (wordValue K s)⁻¹ := by
  induction s with
  | nil => simp only [wordValue, List.reverse_nil, List.map_nil, List.prod_nil, inv_one]
  | cons x s ih =>
    rw [List.reverse_cons, wordValue_append, ih]
    simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_inv_rev, oneRoot_inv]

private theorem wordValue_weyl (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (i : Fin 4) : wordValue K (weylLetters i) = weyl K i := by
  simp only [wordValue, weylLetters, weyl, CharTwo.neg_eq,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

private theorem wordValue_long (K : Type) [_root_.Field K] [Finite K] [CharP K 2] :
    wordValue K longLetters = middleLong K 1 := by
  rw [longLetters, wordValue_append, wordValue_append, wordValue_reverse,
    wordValue_weyl]
  simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, middleLong]

private theorem wordValue_short (K : Type) [_root_.Field K] [Finite K] [CharP K 2] :
    wordValue K shortLetters = middleShort K 1 := by
  rw [shortLetters, wordValue_append, wordValue_append, wordValue_reverse,
    wordValue_weyl]
  simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, middleShort]

theorem outerLetters_value (m : ℕ) :
    wordValue (Field m) outerLetters = (fixedOuterHom m (Multiplicative.ofAdd 1)).val := by
  change wordValue (Field m) outerLetters = outerWord m 1
  simp only [wordValue, outerLetters, outerWord, map_one, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

theorem fourCycleLetters_value (m : ℕ) :
    wordValue (Field m) fourCycleLetters = (fourCycle m).val := by
  rw [fourCycleLetters, wordValue_append, wordValue_long]
  change _ = fixedMiddleWord m 1 0
  rw [fixedMiddleWord_one_zero]
  simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem fiveLetters_value (m : ℕ) :
    wordValue (Field m) fiveLetters = (fiveWord m).val := by
  rw [fiveLetters, wordValue_append, wordValue_append, wordValue_long, wordValue_short]
  have hw : wordValue (Field m) middleWeylLetters = middleRelativeWeyl m := by
    simp only [middleWeylLetters, wordValue_append, wordValue_weyl, middleRelativeWeyl]
  rw [hw]
  change _ = (middleFixedWeyl m).val * ((fourCycle m)^2).val
  rw [fourCycle_square]
  change _ = middleRelativeWeyl m * fixedMiddleWord m 0 1
  rw [fixedMiddleWord_zero_one]
  exact mul_assoc _ _ _

def positiveCommutator (m : ℕ) : originalModelFixed m :=
  ⁅fixedOuterHom m (Multiplicative.ofAdd 1), fourCycle m⁆

theorem positiveCommutator_mem_derived (m : ℕ) :
    positiveCommutator m ∈ commutator (originalModelFixed m) :=
  Subgroup.commutator_mem_commutator (by trivial) (by trivial)

theorem positiveCommutator_mem_positive (m : ℕ) :
    positiveCommutator m ∈ fixedPositive m := by
  have hx : fixedOuterHom m (Multiplicative.ofAdd 1) ∈ fixedPositive m :=
    fixedOuterHom_range_le_fixedPositive m ⟨Multiplicative.ofAdd 1,rfl⟩
  have hy : fourCycle m ∈ fixedPositive m :=
    middleFixedSubgroup_le_fixedPositive m
      ⟨1,alpha m 1,0,alpha m 0+1^2*alpha m 1,rfl⟩
  rw [positiveCommutator, commutatorElement_def]
  exact (fixedPositive m).mul_mem
    ((fixedPositive m).mul_mem ((fixedPositive m).mul_mem hx hy)
      ((fixedPositive m).inv_mem hx)) ((fixedPositive m).inv_mem hy)

def derivedPositiveCommutator (m : ℕ) : derivedPositive m :=
  ⟨⟨positiveCommutator m, positiveCommutator_mem_derived m⟩,
    positiveCommutator_mem_positive m⟩

theorem positiveCommutatorLetters_value (m : ℕ) :
    wordValue (Field m) positiveCommutatorLetters = (positiveCommutator m).val := by
  simp only [positiveCommutatorLetters, wordValue_append, wordValue_reverse,
    outerLetters_value, fourCycleLetters_value]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords
