import SymmetricSubgroupAsymptotics.PrimeDerivedPairIntermediate
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1547
import SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1547

/-! Exact profiles for EVERY original normal of 16T1547 strictly between
its relative derived radical and its derived subgroup. The two cases are
dimensions of the complete actual vanishing space, not an enumeration of
planes and not a claim that every profile is realized. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1547

abbrev Original := BinaryCarrierRadicalProfiles16T1547.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev profile := BinaryCarrierRadicalProfiles16T1547.profile
private abbrev hker := BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator

theorem invariants (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    PrimeDerivedPairIntermediateInvariants 2 hker N 3 2 2 :=
  pairDerived_intermediate_invariants 2 hker
    BinaryCarrierDerivedRadical16T1547.relative_character_rank
    BinaryCarrierFormKernelExact16T1547.actual_form_finrank_ker_eq_two
    BinaryCarrierFormTransport16T1547.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierRadicalSaturation16T1547.certificate
    BinaryCarrierRadicalSaturation16T1547.nonempty_words 3 2 2
    BinaryCarrierDerivedRadical16T1547.card_relative_radical
    BinaryCarrierRadicalProfiles16T1547.head_R
    BinaryCarrierRadicalProfiles16T1547.normalHeadMax_R N hRN hND

/-- The actual order and quotient slopes are retained along with both
heads. In particular m remains a maximum over all original normals. -/
theorem profile_eq (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    profile N =
      (3 - pairIntermediateParameterDimension 2 N,
        3 + (3 - pairIntermediateParameterDimension 2 N),
        max 2 (3 - pairIntermediateParameterDimension 2 N), 2,
        pairIntermediateParameterDimension 2 N +
          (if pairIntermediateParameterDimension 2 N = 1 then 2 else 0),
        pairIntermediateParameterDimension 2 N) := by
  have h := invariants N hRN hND
  unfold profile BinaryCarrierRadicalProfiles16T1547.profile
  rw [h.head_eq, h.card_eq, inf_eq_left.mpr hND.le,
    h.normalHeadMax_eq, h.radicalHead_eq, h.center_card, h.derived_card]
  simp only [Nat.log_pow (by decide : 1 < (2 : ℕ))]

theorem normal_profile (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    profile N = (1,4,2,2,2,2) ∨ profile N = (2,5,2,2,3,1) := by
  have h := invariants N hRN hND
  have hp := profile_eq N hRN hND
  rcases h.parameter_cases with h1 | h2
  · exact Or.inr (by simpa [h1] using hp)
  · exact Or.inl (by simpa [h2] using hp)

end SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1547
