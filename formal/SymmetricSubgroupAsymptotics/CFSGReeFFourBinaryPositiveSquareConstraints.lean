import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSixthConstraint
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareColumns

/-! Reuse of the checked full e2 column. The literal y² probe fixes e2;
its four selected row equations kill bits8,9,10,11 without any additional
symbolic column certificate. Together with X only bits5 and7 remain.
This is a statement about covered ORIGINAL elements, not matrix faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSquareConstraints
open CFSGReeFFourBinaryPositiveSixthConstraint CFSGReeFFourBinaryMiddleSquareColumns
open CFSGReeFFourBinaryFourthGlobalColumn CFSGReeFFourBinaryOrderedMatrixChart
open CFSGReeFFourBinaryOrderedBooleanParameters CFSGReeFFourBinaryOrderedRootWords
open CFSGReeFFourBinaryOrderedMatrixData CFSGReeFFourBinaryFirstGlobalEntry
open CFSGFFourNormPrimeFieldWords CFSGFFourNormPrimeFieldMatrixTransport
open CFSGReeFFourDerivedPositiveFourProbes CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOuterThreeWord CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFieldParameters

private theorem fixed_vector_of_commuting (M X : Mat) (v : Fin 26 → ZMod 2)
    (hv : X.mulVec v=v) (h : Commute M X) :
    X.mulVec (M.mulVec v)=M.mulVec v := by
  calc
    X.mulVec (M.mulVec v)=(X*M).mulVec v := Matrix.mulVec_mulVec v X M
    _=(M*X).mulVec v := congrArg (fun A : Mat => A.mulVec v) h.eq.symm
    _=M.mulVec (X.mulVec v) := (Matrix.mulVec_mulVec v M X).symm
    _=M.mulVec v := congrArg M.mulVec hv

theorem column_two_fixed (b : Fin 12 → ZMod 2)
    (h : Commute (chartMatrix b) middleSquareMatrix) :
    middleSquareMatrix.mulVec (columnTwo b)=columnTwo b := by
  have hh := fixed_vector_of_commuting (chartMatrix b) middleSquareMatrix
    (Pi.single 2 1) middle_square_fix_two h
  rw [chart_column_two] at hh
  exact hh

private theorem bool_scalar_zero (p : Bool)
    (h : ((if p then 1 else 0) : ZMod 2)=0) : p=false := by
  cases p
  · rfl
  · exact False.elim (one_ne_zero h)

theorem square_bits_zero_of_matrix_commute (b : Fin 12 → Bool)
    (h : Commute (chartMatrix (bitValues b)) middleSquareMatrix) :
    b 8=false ∧ b 9=false ∧ b 10=false ∧ b 11=false := by
  have hf := column_two_fixed (bitValues b) h
  have h5 := congrFun hf (5 : Fin 26)
  rw [middle_square_apply_five] at h5
  have hz3 : columnTwo (bitValues b) 3=0 := add_eq_right.mp h5
  have h11 : b 11=false := bool_scalar_zero (b 11) (by
    simpa [columnTwo,bitValues] using hz3)
  have h6 := congrFun hf (6 : Fin 26)
  rw [middle_square_apply_six] at h6
  have hz34 : columnTwo (bitValues b) 3+columnTwo (bitValues b) 4=0 :=
    add_eq_right.mp h6
  have h9 : b 9=false := bool_scalar_zero (b 9) (by
    simpa [columnTwo,bitValues,h11] using hz34)
  have hr9 := congrFun hf (9 : Fin 26)
  rw [middle_square_apply_nine] at hr9
  have hz7 : columnTwo (bitValues b) 7=0 := add_eq_right.mp hr9
  have h10 : b 10=false := bool_scalar_zero (b 10) (by
    simpa [columnTwo,bitValues,h11] using hz7)
  have h23 := congrFun hf (23 : Fin 26)
  rw [middle_square_apply_twentyThree] at h23
  have hz21 : columnTwo (bitValues b) 21=0 := add_eq_right.mp h23
  have h8 : b 8=false := bool_scalar_zero (b 8) (by
    simpa [columnTwo,bitValues,h9,h10,h11] using hz21)
  exact ⟨h8,h9,h10,h11⟩

theorem chart_square_commute (u : originalModelFixed 0) (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hy : Commute u ((fourCycle 0)^2)) :
    Commute (chartMatrix (bitValues b)) middleSquareMatrix := by
  have hv : Commute
      (wordValue (Field 0) (orderedLetters (exponentFunction b) 8))
      (wordValue (Field 0) (probeLetters 2)) := by
    rw [hb]
    have he : wordValue (Field 0) (probeLetters 2)=((fourCycle 0)^2).val :=
      probe_letters_value 0 2
    rw [he]
    exact hy.map (originalModelFixed 0).subtype
  have hm := wordMatrix_commute_of_wordValue_commute (Field 0) _ _ hv
  rw [encoded_word_matrix,probe_two_matrix] at hm
  exact hm

theorem square_bits_zero_of_commute (u : originalModelFixed 0) (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hy : Commute u ((fourCycle 0)^2)) :
    b 8=false ∧ b 9=false ∧ b 10=false ∧ b 11=false :=
  square_bits_zero_of_matrix_commute b (chart_square_commute u b hb hy)

def OuterSquareCode (b : Fin 12 → Bool) : Prop :=
  ∀i : Fin 12,i≠5 → i≠7 → b i=false

theorem outer_square_code_of_commute (u : originalModelFixed 0) (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) (hy : Commute u ((fourCycle 0)^2)) :
    OuterSquareCode b := by
  have hs := first_five_and_six_zero_of_commute u b hb hx
  have ht := square_bits_zero_of_commute u b hb hy
  intro i hi5 hi7
  fin_cases i <;> simp_all

theorem exists_positive_outer_square_code (u : originalModelFixed 0)
    (hu : u∈fixedPositive 0) (hx : Commute u (outerInvolution 0))
    (hy : Commute u ((fourCycle 0)^2)) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val ∧ OuterSquareCode b := by
  obtain ⟨b,hb⟩ := exists_encoded_positive u hu
  exact ⟨b,hb,outer_square_code_of_commute u b hb hx hy⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSquareConstraints
