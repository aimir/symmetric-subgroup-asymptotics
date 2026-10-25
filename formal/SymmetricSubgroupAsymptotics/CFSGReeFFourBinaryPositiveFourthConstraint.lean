import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveThirdConstraint
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFourthGlobalColumn

/-! The remaining outer entry forces bit3 zero, then the checked relation
bit3=bit4 forces bit4 zero. All five zeros refer to the SAME actual
covered positive code. There is no common-centre or Out assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFourthConstraint
open CFSGReeFFourBinaryPositiveSecondConstraint CFSGReeFFourBinaryPositiveThirdConstraint
open CFSGReeFFourBinaryFourthGlobalColumn CFSGReeFFourBinaryOrderedMatrixChart
open CFSGReeFFourBinaryOrderedBooleanParameters CFSGReeFFourBinaryOrderedRootWords
open CFSGReeFFourBinaryOrderedMatrixData CFSGReeFFourBinaryFirstGlobalEntry
open CFSGFFourNormPrimeFieldWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourBinarySeedOuterMatrix

private theorem bool_scalar_zero (p : Bool)
    (h : ((if p then 1 else 0) : ZMod 2)=0) : p=false := by
  cases p
  · rfl
  · exact False.elim (one_ne_zero h)

theorem first_five_bits_zero_of_commute (u : originalModelFixed 0)
    (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) :
    b 0=false ∧ b 1=false ∧ b 2=false ∧ b 3=false ∧ b 4=false := by
  have hs := first_three_bits_zero_of_commute u b hb hx
  have h34 := next_bits_equal_of_commute u b hb hx
  have hm := chart_outer_commute u b hb hx
  have hz : chartMatrix (bitValues b)*outerMatrix-
      outerMatrix*chartMatrix (bitValues b)=0 := sub_eq_zero.mpr hm.eq
  have he := congrArg (fun M : Mat => M 0 2) hz
  change (chartMatrix (bitValues b)*outerMatrix-
    outerMatrix*chartMatrix (bitValues b)) 0 2=0 at he
  rw [fourth_constraint_commutator_entry] at he
  have hv3 : bitValues b 3=0 := by
    simpa [bitValues,hs.1,hs.2.1,hs.2.2] using he
  have h3 : b 3=false := bool_scalar_zero (b 3) hv3
  exact ⟨hs.1,hs.2.1,hs.2.2,h3,h34.symm.trans h3⟩

theorem exists_positive_code_first_five_bits_zero (u : originalModelFixed 0)
    (hu : u∈fixedPositive 0) (hx : Commute u (outerInvolution 0)) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val ∧
        b 0=false ∧ b 1=false ∧ b 2=false ∧ b 3=false ∧ b 4=false := by
  obtain ⟨b,hb⟩ := exists_encoded_positive u hu
  exact ⟨b,hb,first_five_bits_zero_of_commute u b hb hx⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFourthConstraint
