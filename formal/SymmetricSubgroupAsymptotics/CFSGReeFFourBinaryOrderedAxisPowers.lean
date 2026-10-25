import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedPrefixMatrices

/-! Forward/backward prefix matrices are genuine mutual inverses because
the ORIGINAL root words are inverse group words. This transports arbitrary
parameter powers to the same literal conjugated axis matrix, without
using matrix faithfulness, arbitrary group recognition or finite cases. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedAxisPowers
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGReeFFourBinaryOrderedPrefixMatrices CFSGFFourNormPrimeFieldWords
open CFSGFFourNormSparseWordMatrix CFSGFFourNormPrimeFieldMatrixTransport
open CFSGReeFFourFieldParameters CFSGReeFFourBinarySeedOuterMatrix

theorem prefix_back_identity (m : ℕ) (i : Fin 9) :
    prefixMatrix i*backMatrix i=1 := by
  have hv : wordValue (Field m) (prefixLetters i.val++(prefixLetters i.val).reverse)=
      wordValue (Field m) [] := by
    rw [wordValue_append,reversed_letters_value,mul_inv_cancel]
    rfl
  have hm := wordMatrix_eq_of_wordValue_eq (Field m) _ _ hv
  rw [wordMatrix_append] at hm
  change wordMatrix (ZMod 2) (prefixLetters i.val)*
    wordMatrix (ZMod 2) (prefixLetters i.val).reverse=1 at hm
  rw [prefix_matrix i,reversed_prefix_matrix m i] at hm
  exact hm

theorem back_prefix_identity (m : ℕ) (i : Fin 9) :
    backMatrix i*prefixMatrix i=1 := by
  have hv : wordValue (Field m) ((prefixLetters i.val).reverse++prefixLetters i.val)=
      wordValue (Field m) [] := by
    rw [wordValue_append,reversed_letters_value,inv_mul_cancel]
    rfl
  have hm := wordMatrix_eq_of_wordValue_eq (Field m) _ _ hv
  rw [wordMatrix_append] at hm
  change wordMatrix (ZMod 2) (prefixLetters i.val).reverse*
    wordMatrix (ZMod 2) (prefixLetters i.val)=1 at hm
  rw [reversed_prefix_matrix m i,prefix_matrix i] at hm
  exact hm

private theorem matrix_power_of_sandwich_eq (P Q A B : Mat)
    (hB : B=Q*A*P) (hPQ : P*Q=1) (hQP : Q*P=1) (n : ℕ) :
    B^n=Q*A^n*P := by
  rw [hB]
  induction n with
  | zero => simp only [pow_zero,mul_one,hQP]
  | succ n ih =>
    rw [pow_succ,ih,pow_succ]
    calc
      _=Q*A^n*(P*Q)*A*P := by simp only [Matrix.mul_assoc]
      _=Q*(A^n*A)*P := by simp only [hPQ,Matrix.mul_one,Matrix.mul_assoc]

theorem axis_power (m : ℕ) (i : Fin 8) (a : ℕ) :
    (axisMatrix i)^a=backMatrix i.castSucc*
      (if i.val%2=0 then CFSGReeFFourBinarySeedMiddleMatrix.matrix else outerMatrix)^a*
      prefixMatrix i.castSucc := by
  have hB := axis_eq i
  have hPQ := prefix_back_identity m i.castSucc
  have hQP := back_prefix_identity m i.castSucc
  generalize hP : prefixMatrix i.castSucc=P at hB hPQ hQP ⊢
  generalize hQ : backMatrix i.castSucc=Q at hB hPQ hQP ⊢
  generalize hA : (if i.val%2=0 then
    CFSGReeFFourBinarySeedMiddleMatrix.matrix else outerMatrix)=A at hB ⊢
  generalize hC : axisMatrix i=C at hB ⊢
  exact matrix_power_of_sandwich_eq P Q A C hB hPQ hQP a

theorem parameter_block_eq_axis_power (m : ℕ) (i : Fin 8) (a : ℕ) :
    wordMatrix (ZMod 2) ((prefixLetters i.val).reverse++
      (List.replicate a (baseLetters i.val)).flatten++prefixLetters i.val)=
      (axisMatrix i)^a :=
  (parameter_block_matrix m i a).trans (axis_power m i a).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedAxisPowers
