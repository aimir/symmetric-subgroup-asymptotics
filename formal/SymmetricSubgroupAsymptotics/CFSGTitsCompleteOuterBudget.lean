import SymmetricSubgroupAsymptotics.CFSGTitsOuterImagePackedConditions
import SymmetricSubgroupAsymptotics.CFSGReeFFourPackedTailClassification
import SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerOuterEvaluation
import SymmetricSubgroupAsymptotics.CFSGTitsPairStabilizerOuterBound

/-! The actual opposed-Sylow pair stabilizer embeds in the three
kernel-classified literal tail codes. This closes its cardinal target
and the sufficient Tits outer budget from the existing simple-model
hypothesis. No code is interpreted as an arbitrary group element:
the SAME original source word is retained throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsCompleteOuterBudget
open CFSGTitsOuterImagePackedConditions CFSGReeFFourPackedTailClassification
open CFSGTitsPairStabilizerOuterEvaluation CFSGTitsPairStabilizerOuterBound
open CFSGTitsIntrinsicMiddleRadical CFSGTitsAmbientPairAlignment
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalPositiveSylow CFSGFFourNormPrimeFieldWords
open PrimitiveSocleRawStructure
open CFSGReeFFourSignedOuterOddProduct

def candidateCode : Fin 3→Fin 1024 := ![64,512,864]

theorem exists_candidate_source [IsSimpleGroup CFSG.Models.Tits] (f : pairStabilizer) :
    ∃j : Fin 3,∃u : sourceIntersection,
      derivedReeHom 0 u.val=f.val (originalOuterRoot 0) ∧
      wordValue (Field 0) (sourceLetters (candidateCode j))=u.val.val.val := by
  obtain ⟨c,u,hu,hw,hc⟩ := exists_admissible_source f
  rcases code_of_packedAdmissible c hc with h|h|h
  · subst c
    exact ⟨0,u,hu,hw⟩
  · subst c
    exact ⟨1,u,hu,hw⟩
  · subst c
    exact ⟨2,u,hu,hw⟩

private def imageCode [IsSimpleGroup CFSG.Models.Tits] (f : pairStabilizer) : Fin 3 :=
  Classical.choose (exists_candidate_source f)

private theorem imageCode_spec [IsSimpleGroup CFSG.Models.Tits] (f : pairStabilizer) :
    ∃u : sourceIntersection,
      derivedReeHom 0 u.val=f.val (originalOuterRoot 0) ∧
      wordValue (Field 0) (sourceLetters (candidateCode (imageCode f)))=u.val.val.val :=
  Classical.choose_spec (exists_candidate_source f)

private theorem imageCode_injective [IsSimpleGroup CFSG.Models.Tits] :
    Function.Injective imageCode := by
  intro f g h
  obtain ⟨u,hu,hw⟩ := imageCode_spec f
  obtain ⟨v,hv,hvword⟩ := imageCode_spec g
  rw [h] at hw
  have huv : u.val=v.val := Subtype.ext (Subtype.ext (hw.symm.trans hvword))
  apply outerEvaluation_injective
  exact hu.symm.trans ((congrArg (derivedReeHom 0) huv).trans hv)

theorem pairStabilizer_card_le_three [IsSimpleGroup CFSG.Models.Tits] :
    Nat.card pairStabilizer≤3 := by
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective imageCode imageCode_injective

theorem pairStabilizer_card_le_four [IsSimpleGroup CFSG.Models.Tits] :
    Nat.card pairStabilizer≤4 :=
  pairStabilizer_card_le_three.trans (by decide)

theorem outer_card_le_six [IsSimpleGroup CFSG.Models.Tits] :
    Nat.card (Outer CFSG.Models.Tits)≤6 := by
  exact outer_card_le_twice_pairStabilizer.trans
    (Nat.mul_le_mul_left 2 pairStabilizer_card_le_three)

theorem tits_sufficient_outer_budget [IsSimpleGroup CFSG.Models.Tits]
    (ell : ℕ) (hell : LeastProperIndex CFSG.Models.Tits ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Tits)) :=
  outer_budget_of_pairStabilizer_card_le_four ell hell pairStabilizer_card_le_four

end SymmetricSubgroupAsymptotics.CFSGTitsCompleteOuterBudget
