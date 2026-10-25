import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFirstConstraint
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySecondGlobalEntry

/-! The second checked entry removes the third Boolean parameter in the
SAME actual positive code. The column proof is reused, not duplicated.
No original equality is inferred from equality of representation matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSecondConstraint
open CFSGReeFFourBinaryPositiveFirstConstraint CFSGReeFFourBinarySecondGlobalEntry
open CFSGReeFFourBinaryOrderedMatrixChart CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGReeFFourBinaryFirstGlobalEntry CFSGReeFFourBinaryOrderedPrefixMatrices
open CFSGFFourNormPrimeFieldWords CFSGFFourNormPrimeFieldMatrixTransport
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourBinarySeedOuterMatrix

private theorem bool_scalar_zero (p : Bool)
    (h : ((if p then 1 else 0) : ZMod 2)=0) : p=false := by
  cases p
  · rfl
  · exact False.elim (one_ne_zero h)

theorem chart_outer_commute (u : originalModelFixed 0) (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) :
    Commute (chartMatrix (bitValues b)) outerMatrix := by
  have hv : Commute
      (wordValue (Field 0) (orderedLetters (exponentFunction b) 8))
      (wordValue (Field 0) outerLetters) := by
    rw [hb]
    have he : wordValue (Field 0) outerLetters=(outerInvolution 0).val :=
      outerLetters_value 0
    rw [he]
    exact hx.map (originalModelFixed 0).subtype
  have hm := wordMatrix_commute_of_wordValue_commute (Field 0) _ _ hv
  rw [encoded_word_matrix,outer_seed_matrix] at hm
  exact hm

theorem first_three_bits_zero_of_commute (u : originalModelFixed 0)
    (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) :
    b 0=false ∧ b 1=false ∧ b 2=false := by
  have h01 := first_bits_zero_of_commute u b hb hx
  have hm := chart_outer_commute u b hb hx
  have hz : chartMatrix (bitValues b)*outerMatrix-
      outerMatrix*chartMatrix (bitValues b)=0 := sub_eq_zero.mpr hm.eq
  have he := congrArg (fun M : Mat => M 0 4) hz
  change (chartMatrix (bitValues b)*outerMatrix-
    outerMatrix*chartMatrix (bitValues b)) 0 4=0 at he
  rw [second_global_commutator_entry] at he
  have h2 : bitValues b 2=0 := by
    simpa [bitValues,h01.1,h01.2] using he
  exact ⟨h01.1,h01.2,bool_scalar_zero (b 2) h2⟩

theorem exists_positive_code_first_three_bits_zero (u : originalModelFixed 0)
    (hu : u∈fixedPositive 0) (hx : Commute u (outerInvolution 0)) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val ∧
        b 0=false ∧ b 1=false ∧ b 2=false := by
  obtain ⟨b,hb⟩ := exists_encoded_positive u hu
  exact ⟨b,hb,first_three_bits_zero_of_commute u b hb hx⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveSecondConstraint
