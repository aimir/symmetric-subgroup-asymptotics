import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedMatrixChart

/-! A first actual common-centralizer constraint. If an ORIGINAL positive
element commutes with the actual outer involution, its chosen covered
Boolean chart has both first bits zero. This uses only one-way matrix
transport; it does not infer original group equality from matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFirstConstraint
open CFSGReeFFourBinaryOrderedMatrixChart CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGReeFFourBinaryFirstGlobalEntry CFSGReeFFourBinaryOrderedPrefixMatrices
open CFSGFFourNormPrimeFieldWords CFSGFFourNormPrimeFieldMatrixTransport
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourBinarySeedOuterMatrix

private theorem zero_boolean_pair (p q : Bool)
    (h : ((if p then 1 else 0) : ZMod 2)+(if q then 1 else 0)+
      (if p then 1 else 0)*(if q then 1 else 0)=0) : p=false ∧ q=false := by
  have hh : ∀p q : Bool,
      (((if p then 1 else 0) : ZMod 2)+(if q then 1 else 0)+
        (if p then 1 else 0)*(if q then 1 else 0)=0) → p=false ∧ q=false := by
    decide +kernel
  exact hh p q h

theorem first_bits_zero_of_commute (u : originalModelFixed 0)
    (b : Fin 12 → Bool)
    (hb : wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val)
    (hx : Commute u (outerInvolution 0)) : b 0=false ∧ b 1=false := by
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
  have hz : chartMatrix (bitValues b)*outerMatrix-
      outerMatrix*chartMatrix (bitValues b)=0 := sub_eq_zero.mpr hm.eq
  have he := congrArg (fun M : Mat => M 0 7) hz
  change (chartMatrix (bitValues b)*outerMatrix-
    outerMatrix*chartMatrix (bitValues b)) 0 7=0 at he
  rw [first_global_commutator_entry] at he
  exact zero_boolean_pair (b 0) (b 1) he

theorem exists_positive_code_first_bits_zero (u : originalModelFixed 0)
    (hu : u∈fixedPositive 0) (hx : Commute u (outerInvolution 0)) :
    ∃b : Fin 12 → Bool,
      wordValue (Field 0) (orderedLetters (exponentFunction b) 8)=u.val ∧
        b 0=false ∧ b 1=false := by
  obtain ⟨b,hb⟩ := exists_encoded_positive u hu
  exact ⟨b,hb,first_bits_zero_of_commute u b hb hx⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFirstConstraint
