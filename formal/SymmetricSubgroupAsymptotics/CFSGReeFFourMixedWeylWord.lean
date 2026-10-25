import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryAbelianGenerators

/-! Exact literal words and abelian images for a Coxeter-perturbed
middle parameter. No finite period, group order or generation assertion
is made. In particular the exponent thirteen is not a theorem here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMixedWeylWord
open CFSGFFourNormPrimeFieldWords CFSGFFourOriginalMiddleParameterHoms
open CFSGFFourOriginalMiddleWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourBinaryAbelianGenerators
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration

private def weylLetters (i : Fin 4) : List Letter :=
  [(false,i),(true,i),(false,i)]

def middleWeylLetters : List Letter :=
  weylLetters 1 ++ weylLetters 2 ++ weylLetters 1 ++ weylLetters 2

def mixedWeylLetters : List Letter :=
  fourCycleLetters ++ (weylLetters 0 ++ weylLetters 3) ++ middleWeylLetters

def mixedWeylWord (m : ℕ) : originalModelFixed m :=
  fourCycle m * outerFixedWeyl m * middleFixedWeyl m

private theorem weylLetters_value (m : ℕ) (i : Fin 4) :
    wordValue (Field m) (weylLetters i) = weyl (Field m) i := by
  simp only [wordValue, weylLetters, weyl, CharTwo.neg_eq,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem middleWeylLetters_value (m : ℕ) :
    wordValue (Field m) middleWeylLetters = (middleFixedWeyl m).val := by
  simp only [middleWeylLetters, wordValue_append, weylLetters_value]
  rfl

theorem mixedWeylLetters_value (m : ℕ) :
    wordValue (Field m) mixedWeylLetters = (mixedWeylWord m).val := by
  rw [mixedWeylLetters, wordValue_append, wordValue_append, fourCycleLetters_value,
    wordValue_append, weylLetters_value, weylLetters_value, middleWeylLetters_value]
  rfl

theorem mixedWeylLetters_length : mixedWeylLetters.length = 27 := by decide

variable {A : Type*} [CommGroup A]

theorem middleWeyl_image (m : ℕ) (f : originalModelFixed m →* A) :
    f (middleFixedWeyl m) = (f (fourCycle m))^2 := by
  have hc : f (middleFixedWeyl m * fourCycle m * (middleFixedWeyl m)⁻¹) =
      f (fourCycle m) := by
    rw [map_mul, map_mul, map_inv, mul_comm (f (middleFixedWeyl m))
      (f (fourCycle m)), mul_assoc, mul_inv_cancel, mul_one]
  calc
    f (middleFixedWeyl m) = (f (fourCycle m))^2 *
        f (middleFixedWeyl m * fourCycle m * (middleFixedWeyl m)⁻¹) *
          (f (fourCycle m))^3 := by
      conv_lhs => rw [constant_word]
      rw [map_mul, map_mul, map_pow, map_pow]
    _ = (f (fourCycle m))^6 := by
      rw [hc, ← pow_succ, ← pow_add]
    _ = (f (fourCycle m))^2 := by
      calc
        _ = (f (fourCycle m))^4 * (f (fourCycle m))^2 := pow_add _ 4 2
        _ = _ := by rw [← map_pow, fourCycle_four, map_one, one_mul]

theorem mixedWeyl_image (m : ℕ) (f : originalModelFixed m →* A) :
    f (mixedWeylWord m) = (f (fourCycle m))^3 * f (outerInvolution m) := by
  rw [mixedWeylWord, map_mul, map_mul, middleWeyl_image, outerWeyl_image]
  calc
    f (fourCycle m) * f (outerInvolution m) * (f (fourCycle m))^2 =
        (f (fourCycle m))^2 * f (fourCycle m) * f (outerInvolution m) := by
      ac_rfl
    _ = _ := by rw [← pow_succ]

end SymmetricSubgroupAsymptotics.CFSGReeFFourMixedWeylWord
