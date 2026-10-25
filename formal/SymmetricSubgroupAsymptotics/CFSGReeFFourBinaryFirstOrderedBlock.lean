import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveOrderedParameters
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords

/-! Semantic binding for the ONE selected first ordered parameter block.
The other seven block parameters are identity. Its exact original value
is y^a, and its genuine norm26 action is the checked sparse word repeated
a times. No numerical commutator entry or full-chart certificate is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstOrderedBlock
open CFSGOpposedPeelingOrderedParameters CFSGOpposedSubgroupPeelingChain
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourInversionPeelingWords CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGFFourNormPrimeFieldWords
open CFSGFFourNormCertificateAction CFSGFFourOriginalFoldedEquivalence

private theorem ordered_first {G : Type*} [Group G] (w : ℕ → G) (g : G) :
    orderedProduct w 8 (Pi.mulSingle 0 g)=g := by
  simp [orderedProduct,wordPrefix]

def firstParameters (a : Fin 4) : Fin 8 → originalModelFixed 0 :=
  Pi.mulSingle 0 ((fourCycle 0)^a.val)

theorem first_ordered_value (a : Fin 4) :
    orderedProduct (step 0 true) 8 (firstParameters a)=(fourCycle 0)^a.val :=
  ordered_first (step 0 true) ((fourCycle 0)^a.val)

def firstLetters (a : Fin 4) : List Letter :=
  (List.replicate a.val fourCycleLetters).flatten

private theorem repeated_word_value (K : Type) [_root_.Field K]
    (s : List Letter) (n : ℕ) :
    wordValue K ((List.replicate n s).flatten)=(wordValue K s)^n := by
  induction n with
  | zero => simp only [List.replicate_zero,List.flatten_nil,wordValue,
      List.map_nil,List.prod_nil,pow_zero]
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,wordValue_append,ih,pow_succ']

theorem first_letters_value (m : ℕ) (a : Fin 4) :
    wordValue (Field m) (firstLetters a)=((fourCycle m)^a.val).val := by
  rw [firstLetters,repeated_word_value,fourCycleLetters_value]
  rfl

theorem first_ordered_action (a : Fin 4) (v : Fin 26 → Field 0) :
    linearAction (Field 0) (modelEquivFolded (Field 0)
      (orderedProduct (step 0 true) 8 (firstParameters a)).val) v=
        evaluate (Field 0) (firstLetters a) v := by
  have hv : (orderedProduct (step 0 true) 8 (firstParameters a)).val=
      wordValue (Field 0) (firstLetters a) :=
    (congrArg (fun g : originalModelFixed 0 => g.val) (first_ordered_value a)).trans
      (first_letters_value 0 a).symm
  rw [hv]
  exact wordValue_action (Field 0) (firstLetters a) v

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryFirstOrderedBlock
