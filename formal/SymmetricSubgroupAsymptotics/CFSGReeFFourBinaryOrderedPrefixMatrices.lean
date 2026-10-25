import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedRootWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixData
import SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldMatrixTransport

/-! The checked literal matrix tables are the SAME forward and reversed
root-list prefixes in the original ordered chart. Inverse-prefix equality
is transferred one-way from actual original Weyl involutions, for arbitrary
m; no faithfulness or numeric coordinate equality is used for group identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedPrefixMatrices
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGFFourNormPrimeFieldWords CFSGFFourNormSparseWordMatrix
open CFSGFFourNormPrimeFieldMatrixTransport CFSGReeFFourMiddleDerivedFiveRootWords
open CFSGReeFFourBinarySeedOuterMatrix CFSGReeFFourInversionPeelingWords
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence

theorem outer_seed_matrix : wordMatrix (ZMod 2) outerLetters=outerMatrix :=
  wordMatrix_eq_of_basis (ZMod 2) outerLetters outerMatrix outer_matrix_entry

theorem middle_seed_matrix : wordMatrix (ZMod 2) fourCycleLetters=
    CFSGReeFFourBinarySeedMiddleMatrix.matrix := by
  rw [←CFSGReeFFourBinarySeedMiddleMatrix.letters_eq_fourCycle]
  exact wordMatrix_eq_of_basis (ZMod 2) _ _
    CFSGReeFFourBinarySeedMiddleMatrix.matrix_entry

theorem outer_weyl_seed_matrix :
    wordMatrix (ZMod 2) CFSGReeFFourBinarySeedOuterWeylMatrix.letters=
      CFSGReeFFourBinarySeedOuterWeylMatrix.matrix :=
  wordMatrix_eq_of_basis (ZMod 2) _ _ CFSGReeFFourBinarySeedOuterWeylMatrix.matrix_entry

theorem middle_weyl_seed_matrix :
    wordMatrix (ZMod 2) CFSGReeFFourBinarySeedMiddleWeylMatrix.letters=
      CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix :=
  wordMatrix_eq_of_basis (ZMod 2) _ _ CFSGReeFFourBinarySeedMiddleWeylMatrix.matrix_entry

theorem step_matrix (n : ℕ) :
    wordMatrix (ZMod 2) (stepLetters n)=stepMatrix n := by
  by_cases hn : n%2=0
  · simpa only [stepLetters,stepMatrix,hn,if_true] using middle_weyl_seed_matrix
  · simpa only [stepLetters,stepMatrix,hn,if_false] using outer_weyl_seed_matrix

theorem base_matrix (n : ℕ) :
    wordMatrix (ZMod 2) (baseLetters n)=
      if n%2=0 then CFSGReeFFourBinarySeedMiddleMatrix.matrix else outerMatrix := by
  by_cases hn : n%2=0
  · simpa only [baseLetters,hn,if_true] using middle_seed_matrix
  · simpa only [baseLetters,hn,if_false] using outer_seed_matrix

theorem reversed_step_matrix (m n : ℕ) :
    wordMatrix (ZMod 2) (stepLetters n).reverse=stepMatrix n := by
  have hv : wordValue (Field m) (stepLetters n).reverse=
      wordValue (Field m) (stepLetters n) := by
    simp only [reversed_letters_value,step_letters_value]
    exact congrArg (fun g : originalModelFixed m => g.val) (step_inv m true n)
  exact (wordMatrix_eq_of_wordValue_eq (Field m) _ _ hv).trans (step_matrix n)

private def prefixRec : ℕ → Mat
  | 0 => 1
  | n+1 => stepMatrix n*prefixRec n

private def backRec : ℕ → Mat
  | 0 => 1
  | n+1 => backRec n*stepMatrix n

private theorem prefix_rec (n : ℕ) :
    wordMatrix (ZMod 2) (prefixLetters n)=prefixRec n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixLetters,wordMatrix_append,step_matrix,ih]
    rfl

private theorem back_rec (m n : ℕ) :
    wordMatrix (ZMod 2) (prefixLetters n).reverse=backRec n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixLetters,List.reverse_append,wordMatrix_append,ih,reversed_step_matrix m n]
    rfl

theorem prefix_matrix (i : Fin 9) :
    wordMatrix (ZMod 2) (prefixLetters i.val)=prefixMatrix i := by
  rw [prefix_rec]
  induction i using Fin.induction with
  | zero => exact prefix_zero.symm
  | succ j ih =>
    change stepMatrix j.val*prefixRec j.val=prefixMatrix j.succ
    simp only [Fin.val_castSucc] at ih
    rw [ih]
    exact (prefix_step j).symm

theorem reversed_prefix_matrix (m : ℕ) (i : Fin 9) :
    wordMatrix (ZMod 2) (prefixLetters i.val).reverse=backMatrix i := by
  rw [back_rec m]
  induction i using Fin.induction with
  | zero => exact back_zero.symm
  | succ j ih =>
    change backRec j.val*stepMatrix j.val=backMatrix j.succ
    simp only [Fin.val_castSucc] at ih
    rw [ih]
    exact (back_step j).symm

theorem repeated_word_matrix (s : List Letter) (n : ℕ) :
    wordMatrix (ZMod 2) ((List.replicate n s).flatten)=
      (wordMatrix (ZMod 2) s)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,wordMatrix_append,ih,pow_succ']

theorem parameter_block_matrix (m : ℕ) (i : Fin 8) (a : ℕ) :
    wordMatrix (ZMod 2) ((prefixLetters i.val).reverse++
      (List.replicate a (baseLetters i.val)).flatten++prefixLetters i.val)=
      backMatrix i.castSucc*
        (if i.val%2=0 then CFSGReeFFourBinarySeedMiddleMatrix.matrix else outerMatrix)^a*
        prefixMatrix i.castSucc := by
  simp only [wordMatrix_append,repeated_word_matrix,base_matrix]
  have hback := reversed_prefix_matrix m i.castSucc
  have hprefix := prefix_matrix i.castSucc
  simp only [Fin.val_castSucc] at hback hprefix
  rw [hback,hprefix]

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedPrefixMatrices
