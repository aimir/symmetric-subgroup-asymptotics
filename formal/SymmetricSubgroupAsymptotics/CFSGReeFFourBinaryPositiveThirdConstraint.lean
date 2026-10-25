import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSecondConstraint
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryThirdGlobalColumn

/-! The checked e3 column gives equality of bits3 and4 on the SAME actual
covered code. Neither bit is asserted zero; that needs the other entry. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveThirdConstraint
open CFSGReeFFourBinaryPositiveSecondConstraint CFSGReeFFourBinaryThirdGlobalColumn
open CFSGReeFFourBinaryOrderedMatrixChart CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGReeFFourBinaryFirstGlobalEntry CFSGFFourNormPrimeFieldWords
open CFSGReeFFourOuterThreeWord CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFieldParameters
open CFSGReeFFourBinarySeedOuterMatrix

private theorem equal_of_bool_sum_zero (p q : Bool)
    (h : ((if p then 1 else 0) : ZMod 2)+(if q then 1 else 0)=0) : p=q := by
  have hh : ∀p q : Bool,
      (((if p then 1 else 0) : ZMod 2)+(if q then 1 else 0)=0) → p=q := by
    decide +kernel
  exact hh p q h

theorem next_bits_equal_of_commute (u : originalModelFixed 0) (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) : b 3=b 4 := by
  have hs := first_three_bits_zero_of_commute u b hb hx
  have hm := chart_outer_commute u b hb hx
  have hz : chartMatrix (bitValues b)*outerMatrix-
      outerMatrix*chartMatrix (bitValues b)=0 := sub_eq_zero.mpr hm.eq
  have he := congrArg (fun M : Mat => M 1 2) hz
  change (chartMatrix (bitValues b)*outerMatrix-
    outerMatrix*chartMatrix (bitValues b)) 1 2=0 at he
  rw [third_constraint_commutator_entry] at he
  have hh : bitValues b 3+bitValues b 4=0 := by
    simpa [bitValues,hs.1,hs.2.1,hs.2.2] using he
  exact equal_of_bool_sum_zero (b 3) (b 4) hh

theorem first_three_zero_next_equal_of_commute (u : originalModelFixed 0)
    (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) :
    b 0=false ∧ b 1=false ∧ b 2=false ∧ b 3=b 4 := by
  have hs := first_three_bits_zero_of_commute u b hb hx
  exact ⟨hs.1,hs.2.1,hs.2.2,next_bits_equal_of_commute u b hb hx⟩

theorem exists_positive_code_first_three_zero_next_equal
    (u : originalModelFixed 0) (hu : u∈fixedPositive 0)
    (hx : Commute u (outerInvolution 0)) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val ∧
        b 0=false ∧ b 1=false ∧ b 2=false ∧ b 3=b 4 := by
  obtain ⟨b,hb⟩ := exists_encoded_positive u hu
  exact ⟨b,hb,first_three_zero_next_equal_of_commute u b hb hx⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveThirdConstraint
