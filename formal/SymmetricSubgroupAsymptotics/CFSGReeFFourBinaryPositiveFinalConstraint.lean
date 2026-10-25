import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSquareConstraints
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryConjugateOuterColumns

/-! Final literal bit constraint from the SAME three whole derived probes.
Commutation with y² determines the needed e6 entry from the proved e4
column; the selected yxy^-1 row/column then kills bit5. No new polynomial
column, finite tuple census or representation-faithfulness claim occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFinalConstraint
open CFSGReeFFourBinaryPositiveSquareConstraints CFSGReeFFourBinaryConjugateOuterColumns
open CFSGReeFFourBinaryMiddleSquareColumns CFSGReeFFourBinarySecondGlobalEntry
open CFSGReeFFourBinaryThirdGlobalColumn CFSGReeFFourBinaryFourthGlobalColumn
open CFSGReeFFourBinaryOrderedMatrixChart CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGReeFFourBinaryFirstGlobalEntry CFSGFFourNormPrimeFieldWords
open CFSGFFourNormPrimeFieldMatrixTransport CFSGReeFFourDerivedPositiveFourProbes
open CFSGReeFFourMiddleDerivedFiveWord CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters
open scoped BigOperators

private theorem selected_row_apply (A : Mat) (i : Fin 26) (S : Finset (Fin 26))
    (h : ∀k,A i k=if k∈S then 1 else 0) (v : Fin 26 → ZMod 2) :
    (A.mulVec v) i=∑k∈S,v k := by
  change (∑k : Fin 26,A i k*v k)=∑k∈S,v k
  simp_rw [h]
  simp [ite_mul]

theorem conjugate_outer_apply_one (v : Fin 26 → ZMod 2) :
    (conjugateOuterMatrix.mulVec v) 1=v 1+v 3+v 5+v 6+v 9+v 11 := by
  simpa [add_assoc] using selected_row_apply conjugateOuterMatrix 1
    {1,3,5,6,9,11} conjugate_outer_row_one v

theorem conjugate_outer_apply_two :
    conjugateOuterMatrix.mulVec (Pi.single 2 1)=
      Pi.single 2 1+Pi.single 3 1+Pi.single 4 1+Pi.single 6 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change conjugateOuterMatrix i 2=_
  rw [conjugate_outer_column_two]
  fin_cases i <;> rfl

private theorem commuting_mulVec (M X : Mat) (h : Commute M X)
    (v : Fin 26 → ZMod 2) : M.mulVec (X.mulVec v)=X.mulVec (M.mulVec v) := by
  calc
    M.mulVec (X.mulVec v)=(M*X).mulVec v := Matrix.mulVec_mulVec v M X
    _=(X*M).mulVec v := congrArg (fun A : Mat => A.mulVec v) h.eq
    _=X.mulVec (M.mulVec v) := (Matrix.mulVec_mulVec v X M).symm

theorem chart_one_six_of_square_commute (b : Fin 12 → ZMod 2)
    (h : Commute (chartMatrix b) middleSquareMatrix) :
    chartMatrix b 1 6=columnFour b 12 := by
  have hc := commuting_mulVec (chartMatrix b) middleSquareMatrix h (Pi.single 4 1)
  simp only [middle_square_apply_four,Matrix.mulVec_add,chart_column_four] at hc
  have hr := congrFun hc (1 : Fin 26)
  simp only [Pi.add_apply,middle_square_apply_one] at hr
  have he : ((chartMatrix b).mulVec (Pi.single 6 1)) 1=columnFour b 12 :=
    add_left_cancel hr
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using he

private theorem bool_scalar_zero (p : Bool)
    (h : ((if p then 1 else 0) : ZMod 2)=0) : p=false := by
  cases p
  · rfl
  · exact False.elim (one_ne_zero h)

theorem bit_five_zero_of_matrix_commute (b : Fin 12 → Bool)
    (hcode : OuterSquareCode b)
    (hsquare : Commute (chartMatrix (bitValues b)) middleSquareMatrix)
    (hconj : Commute (chartMatrix (bitValues b)) conjugateOuterMatrix) : b 5=false := by
  have hc := commuting_mulVec (chartMatrix (bitValues b)) conjugateOuterMatrix
    hconj (Pi.single 2 1)
  simp only [conjugate_outer_apply_two,Matrix.mulVec_add,
    chart_column_two,chart_column_three,chart_column_four] at hc
  have hr := congrFun hc (1 : Fin 26)
  simp only [Pi.add_apply,conjugate_outer_apply_one,
    Matrix.mulVec_single_one,Matrix.col_apply] at hr
  rw [chart_one_six_of_square_commute (bitValues b) hsquare] at hr
  have hb0 := hcode 0 (by decide) (by decide)
  have hb1 := hcode 1 (by decide) (by decide)
  have hb2 := hcode 2 (by decide) (by decide)
  have hb3 := hcode 3 (by decide) (by decide)
  have hb4 := hcode 4 (by decide) (by decide)
  have hb6 := hcode 6 (by decide) (by decide)
  have hb8 := hcode 8 (by decide) (by decide)
  have hb9 := hcode 9 (by decide) (by decide)
  have hb10 := hcode 10 (by decide) (by decide)
  have hb11 := hcode 11 (by decide) (by decide)
  have he : bitValues b 7=bitValues b 7+bitValues b 5 := by
    simpa [columnTwo,columnThree,columnFour,bitValues,
      hb0,hb1,hb2,hb3,hb4,hb6,hb8,hb9,hb10,hb11] using hr
  have hv : bitValues b 5=0 := add_eq_left.mp he.symm
  exact bool_scalar_zero (b 5) hv

theorem chart_conjugate_commute (u : originalModelFixed 0) (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hconj : Commute u (probes 0 1)) :
    Commute (chartMatrix (bitValues b)) conjugateOuterMatrix := by
  have hv : Commute
      (wordValue (Field 0) (orderedLetters (exponentFunction b) 8))
      (wordValue (Field 0) (probeLetters 1)) := by
    rw [hb,probe_letters_value]
    exact hconj.map (originalModelFixed 0).subtype
  have hm := wordMatrix_commute_of_wordValue_commute (Field 0) _ _ hv
  rw [encoded_word_matrix,probe_one_matrix] at hm
  exact hm

def CentralCode (b : Fin 12 → Bool) : Prop := ∀i : Fin 12,i≠7 → b i=false

theorem central_code_of_commute (u : originalModelFixed 0) (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) (hy : Commute u ((fourCycle 0)^2))
    (hconj : Commute u (probes 0 1)) : CentralCode b := by
  have hcode := outer_square_code_of_commute u b hb hx hy
  have h5 := bit_five_zero_of_matrix_commute b hcode
    (chart_square_commute u b hb hy) (chart_conjugate_commute u b hb hconj)
  intro i hi7
  by_cases hi5 : i=5
  · subst i
    exact h5
  · exact hcode i hi5 hi7

theorem exists_positive_central_code (u : originalModelFixed 0)
    (hu : u∈fixedPositive 0) (hx : Commute u (outerInvolution 0))
    (hy : Commute u ((fourCycle 0)^2)) (hconj : Commute u (probes 0 1)) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val ∧ CentralCode b := by
  obtain ⟨b,hb⟩ := exists_encoded_positive u hu
  exact ⟨b,hb,central_code_of_commute u b hb hx hy hconj⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFinalConstraint
