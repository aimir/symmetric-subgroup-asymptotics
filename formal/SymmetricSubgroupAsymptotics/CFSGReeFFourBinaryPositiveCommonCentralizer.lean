import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveFinalConstraint

/-! An actual common centralizer has at most two elements. The injection
uses chosen ORIGINAL root-word codes, not the norm representation. The
three probes need not generate the positive or derived-positive group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCommonCentralizer
open CFSGReeFFourBinaryPositiveFinalConstraint CFSGReeFFourBinaryOrderedBooleanParameters
open CFSGReeFFourBinaryOrderedRootWords CFSGFFourNormPrimeFieldWords
open CFSGReeFFourDerivedPositiveFourProbes CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOuterThreeWord CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFieldParameters

def CommonCentralizer := {u : originalModelFixed 0 //
  u∈fixedPositive 0 ∧ Commute u (outerInvolution 0) ∧
    Commute u ((fourCycle 0)^2) ∧ Commute u (probes 0 1)}

private def chosenBits (u : CommonCentralizer) : Fin 12 → Bool :=
  Classical.choose (exists_positive_central_code u.val u.property.1
    u.property.2.1 u.property.2.2.1 u.property.2.2.2)

private theorem chosen_value (u : CommonCentralizer) :
    wordValue (Field 0) (orderedLetters (exponentFunction (chosenBits u)) 8)=u.val.val :=
  (Classical.choose_spec (exists_positive_central_code u.val u.property.1
    u.property.2.1 u.property.2.2.1 u.property.2.2.2)).1

private theorem chosen_central (u : CommonCentralizer) : CentralCode (chosenBits u) :=
  (Classical.choose_spec (exists_positive_central_code u.val u.property.1
    u.property.2.1 u.property.2.2.1 u.property.2.2.2)).2

def parameterCode (u : CommonCentralizer) : Bool := chosenBits u 7

theorem parameterCode_injective : Function.Injective parameterCode := by
  intro a b hab
  change chosenBits a 7=chosenBits b 7 at hab
  have he : chosenBits a=chosenBits b := by
    funext i
    by_cases hi : i=7
    · subst i
      exact hab
    · rw [chosen_central a i hi,chosen_central b i hi]
  have hw := congrArg (fun c : Fin 12 → Bool =>
    wordValue (Field 0) (orderedLetters (exponentFunction c) 8)) he
  have hraw : a.val.val=b.val.val :=
    (chosen_value a).symm.trans (hw.trans (chosen_value b))
  apply Subtype.ext
  exact Subtype.ext hraw

theorem card_commonCentralizer_le_two : Nat.card CommonCentralizer ≤ 2 := by
  have h := Nat.card_le_card_of_injective parameterCode parameterCode_injective
  have hc : Nat.card Bool=2 := by simp [Nat.card_eq_fintype_card]
  exact h.trans_eq hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryPositiveCommonCentralizer
