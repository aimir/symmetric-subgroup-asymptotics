import SymmetricSubgroupAsymptotics.PrimeDerivedPairIntermediate
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1084

/-! Every original normal strictly between R_D and D in 16T1084
has one of two exact six-field profiles. The complete vanishing space
determines the case. No list, count or realization of planes is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1084

abbrev Original := BinaryCarrierRadicalProfiles16T1084.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev profile := BinaryCarrierRadicalProfiles16T1084.profile
private abbrev hker := BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator

theorem invariants (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    PrimeDerivedPairIntermediateInvariants 2 hker N 1 1 1 :=
  pairDerived_intermediate_invariants 2 hker
    BinaryCarrierDerivedRadical16T1084.relative_character_rank
    BinaryCarrierFormKernelExact16T1084.actual_form_finrank_ker_eq_two
    BinaryCarrierFormTransport16T1084.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierRadicalSaturation16T1084.certificate
    BinaryCarrierRadicalSaturation16T1084.nonempty_words 1 1 1
    BinaryCarrierDerivedRadical16T1084.card_relative_radical
    BinaryCarrierRadicalProfiles16T1084.relativeHead_eq_one
    BinaryCarrierRadicalProfiles16T1084.normalHeadMax_eq_one N hRN hND

theorem profile_eq (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    profile N =
      (3 - pairIntermediateParameterDimension 2 N,
        1 + (3 - pairIntermediateParameterDimension 2 N),
        max 1 (3 - pairIntermediateParameterDimension 2 N), 1,
        pairIntermediateParameterDimension 2 N +
          (if pairIntermediateParameterDimension 2 N = 1 then 2 else 0),
        pairIntermediateParameterDimension 2 N) := by
  have h := invariants N hRN hND
  change PrimeDerivedOrderTwoProfiles.profile N = _
  unfold PrimeDerivedOrderTwoProfiles.profile
  rw [h.head_eq, h.card_eq, inf_eq_left.mpr hND.le,
    h.normalHeadMax_eq, h.radicalHead_eq, h.center_card, h.derived_card]
  simp only [Nat.log_pow (by decide : 1 < (2 : ℕ))]

/-- Same original subgroup in every field, with m over all original
normals inside its actual derived intersection. -/
theorem normal_profile (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    profile N = (1,2,1,1,2,2) ∨ profile N = (2,3,2,1,3,1) := by
  have h := invariants N hRN hND
  have hp := profile_eq N hRN hND
  rcases h.parameter_cases with h1 | h2
  · exact Or.inr (by simpa [h1] using hp)
  · exact Or.inl (by simpa [h2] using hp)

end SymmetricSubgroupAsymptotics.BinaryCarrierPairIntermediate16T1084

