import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFourthConstraint

/-! Reuse of the checked FULL e4 column: commutation with X fixes this
column. Its row12 equation forces bit6 zero after bits0,1,3 are zero.
No additional symbolic column, word, tuple table or matrix product occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSixthConstraint
open CFSGReeFFourBinaryPositiveFourthConstraint CFSGReeFFourBinaryPositiveSecondConstraint
open CFSGReeFFourBinarySecondGlobalEntry CFSGReeFFourBinaryOrderedMatrixChart
open CFSGReeFFourBinaryOrderedBooleanParameters CFSGReeFFourBinaryOrderedRootWords
open CFSGReeFFourBinaryOrderedMatrixData CFSGReeFFourBinaryFirstGlobalEntry
open CFSGFFourNormPrimeFieldWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourBinarySeedOuterMatrix
open scoped BigOperators

private theorem outer_row_twelve : ∀k : Fin 26,
    outerMatrix 12 k=(if k=6 then 1 else 0)+(if k=8 then 1 else 0)+
      (if k=11 then 1 else 0)+(if k=12 then 1 else 0) := by
  decide +kernel

theorem outer_apply_twelve (v : Fin 26 → ZMod 2) :
    (outerMatrix.mulVec v) 12=v 6+v 8+v 11+v 12 := by
  change (∑k : Fin 26,outerMatrix 12 k*v k)=v 6+v 8+v 11+v 12
  simp_rw [outer_row_twelve]
  simp [add_mul,ite_mul,Finset.sum_add_distrib]

private theorem fixed_vector_of_commuting (M X : Mat) (v : Fin 26 → ZMod 2)
    (hv : X.mulVec v=v) (h : Commute M X) :
    X.mulVec (M.mulVec v)=M.mulVec v := by
  calc
    X.mulVec (M.mulVec v)=(X*M).mulVec v := Matrix.mulVec_mulVec v X M
    _=(M*X).mulVec v := congrArg (fun A : Mat => A.mulVec v) h.eq.symm
    _=M.mulVec (X.mulVec v) := (Matrix.mulVec_mulVec v M X).symm
    _=M.mulVec v := congrArg M.mulVec hv

theorem column_four_fixed (b : Fin 12 → ZMod 2)
    (h : Commute (chartMatrix b) outerMatrix) :
    outerMatrix.mulVec (columnFour b)=columnFour b := by
  have hv : outerMatrix.mulVec (Pi.single 4 1)=Pi.single 4 1 := by
    funext i
    have hi := outer_column_four i
    simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.single_apply,eq_comm] using hi
  have hh := fixed_vector_of_commuting (chartMatrix b) outerMatrix (Pi.single 4 1) hv h
  rw [chart_column_four] at hh
  exact hh

private theorem bool_scalar_zero (p : Bool)
    (h : ((if p then 1 else 0) : ZMod 2)=0) : p=false := by
  cases p
  · rfl
  · exact False.elim (one_ne_zero h)

theorem bit_six_zero_of_matrix_commute (b : Fin 12 → Bool)
    (h : Commute (chartMatrix (bitValues b)) outerMatrix)
    (h0 : b 0=false) (h1 : b 1=false) (h3 : b 3=false) : b 6=false := by
  have hr := congrFun (column_four_fixed (bitValues b) h) (12 : Fin 26)
  rw [outer_apply_twelve] at hr
  have hz : columnFour (bitValues b) 6+columnFour (bitValues b) 8+
      columnFour (bitValues b) 11=0 := add_eq_right.mp hr
  have hs : bitValues b 6=0 := by
    simpa [columnFour,bitValues,h0,h1,h3] using hz
  exact bool_scalar_zero (b 6) hs

theorem first_five_and_six_zero_of_commute (u : originalModelFixed 0)
    (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) :
    b 0=false ∧ b 1=false ∧ b 2=false ∧ b 3=false ∧ b 4=false ∧ b 6=false := by
  have hs := first_five_bits_zero_of_commute u b hb hx
  have h6 := bit_six_zero_of_matrix_commute b (chart_outer_commute u b hb hx)
    hs.1 hs.2.1 hs.2.2.2.1
  exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,h6⟩

theorem exists_positive_code_first_five_and_six_zero
    (u : originalModelFixed 0) (hu : u∈fixedPositive 0)
    (hx : Commute u (outerInvolution 0)) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val ∧
        b 0=false ∧ b 1=false ∧ b 2=false ∧ b 3=false ∧ b 4=false ∧ b 6=false := by
  obtain ⟨b,hb⟩ := exists_encoded_positive u hu
  exact ⟨b,hb,first_five_and_six_zero_of_commute u b hb hx⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSixthConstraint
