import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedReflectionConstants
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedAxisPowers
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterCentralizingReflection

/-! Bind the two fixed compact constants to literal original words, for
all parameters before the binary specialization.  Only whole fixed-group
words are used.  The middle reflection is Wm*y²*Wm inverse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPackedFixedWordSemantics
open BinaryPackedMatrix CFSGReeFFourPackedReflectionConstants
open CFSGReeFFourBinaryOrderedAxisPowers CFSGReeFFourBinaryOrderedPrefixMatrices
open CFSGReeFFourBinaryOrderedMatrixData CFSGReeFFourBinaryOrderedRootWords
open CFSGFFourNormPrimeFieldWords CFSGFFourNormSparseWordMatrix
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOuterCentralizingReflection CFSGReeFFourInversionPeelingWords
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourOppositionFixedPositiveNegative

private theorem conjugate_product {G : Type*} [Group G] (w t : G) :
    (w*t)*t*(w*t)⁻¹=w*t*w⁻¹ := by group

private theorem reflection_conjugate (m : ℕ) :
    reflectionWord m=middleFixedWeyl m*(fourCycle m)^2*(middleFixedWeyl m)⁻¹ :=
  conjugate_product (middleFixedWeyl m) ((fourCycle m)^2)

def reflectionLetters : List Letter :=
  CFSGReeFFourBinarySeedMiddleWeylMatrix.letters++
    (fourCycleLetters++fourCycleLetters)++
      CFSGReeFFourBinarySeedMiddleWeylMatrix.letters.reverse

theorem reflectionLetters_value (m : ℕ) :
    wordValue (Field m) reflectionLetters=(reflectionWord m).val := by
  rw [reflectionLetters,wordValue_append,wordValue_append,wordValue_append,
    reversed_letters_value,middle_weyl_letters_value,fourCycleLetters_value]
  have hv := congrArg (fun g : originalModelFixed m=>g.val) (reflection_conjugate m)
  change (middleFixedWeyl m).val*((fourCycle m).val*(fourCycle m).val)*
    ((middleFixedWeyl m).val)⁻¹=(reflectionWord m).val
  simpa only [pow_two] using hv.symm

private theorem square_matrix :
    CFSGReeFFourBinarySeedMiddleMatrix.matrix^
      (2 : ℕ)=bitMatrix 1 := by
  have hb := congrFun bitMatrix_eq (1 : Fin 12)
  change bitMatrix 1=axisMatrix 0*axisMatrix 0 at hb
  have ha := axis_power 0 (0 : Fin 8) 2
  change (axisMatrix 0)^2=backMatrix 0*
    CFSGReeFFourBinarySeedMiddleMatrix.matrix^2*prefixMatrix 0 at ha
  rw [back_zero,prefix_zero,Matrix.one_mul,Matrix.mul_one] at ha
  exact ha.symm.trans (by simpa only [pow_two] using hb.symm)

theorem reflectionLetters_matrix :
    wordMatrix (ZMod 2) reflectionLetters=decode packedReflection := by
  have hi := reversed_step_matrix 0 0
  change wordMatrix (ZMod 2)
    CFSGReeFFourBinarySeedMiddleWeylMatrix.letters.reverse=
      CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix at hi
  rw [reflectionLetters,wordMatrix_append,wordMatrix_append,wordMatrix_append,
    hi,middle_weyl_seed_matrix,middle_seed_matrix,
    decode_packedReflection]
  rw [←pow_two,square_matrix]

theorem oppositionLetters_value (m : ℕ) :
    wordValue (Field m) (prefixLetters 8)=(oppositionFixed m).val := by
  rw [prefix_letters_value,eighth_prefix_eq_opposition]

end SymmetricSubgroupAsymptotics.CFSGReeFFourPackedFixedWordSemantics
