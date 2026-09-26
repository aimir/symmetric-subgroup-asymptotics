import SymmetricSubgroupAsymptotics.PrimeDerivedStarIntermediate
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierStarTransport16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1332

/-! Exact profiles of every original 16T1332 normal strictly between its
relative derived radical and D. The parameter is the actual invariant head,
and the complete vanishing-character space has complementary dimension.
No list, count or realization of intermediate subspaces is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierStarIntermediate16T1332

abbrev Original := BinaryCarrierRadicalProfiles16T1332.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev profile := BinaryCarrierRadicalProfiles16T1332.profile
private abbrev hker := BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator

def headDimension (N : Subgroup Original) [N.Normal] : ℕ :=
  Module.finrank (ZMod 2) (primeRelativeCharacters 2 N)

theorem invariants (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    PrimeDerivedStarIntermediateInvariants 2 hker N 2 1 1 4 :=
  starDerived_intermediate_invariants 2 hker
    BinaryCarrierStarTransport16T1332.characterEquiv
    BinaryCarrierStarTransport16T1332.evaluationEquiv
    BinaryCarrierStarTransport16T1332.actual_form_eq_star 4 (by simp)
    BinaryCarrierRadicalSaturation16T1332.certificate
    BinaryCarrierRadicalSaturation16T1332.nonempty_words 2 1 1
    BinaryCarrierDerivedRadical16T1332.card_relative_radical
    BinaryCarrierRadicalProfiles16T1332.head_R
    BinaryCarrierRadicalProfiles16T1332.normalHeadMax_R N hRN hND

theorem head_cases (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    headDimension N = 1 ∨ headDimension N = 2 ∨ headDimension N = 3 := by
  have h := invariants N hRN hND
  have hpos : 1 ≤ headDimension N := h.head_pos
  have hlt : headDimension N < 4 := h.head_lt
  omega

theorem vanishingDimension_eq (N : Subgroup Original) [N.Normal]
    (hRN : R < N) (hND : N < D) :
    Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 N) = 4 - headDimension N := by
  have h := (invariants N hRN hND).parameter_add_head
  change Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 N) + headDimension N = 4 at h
  omega

/-- The same original N has exact row (t,2+t,t,1,4,4−t), where
t is its actual whole-group invariant head, not a supplied profile label. -/
theorem profile_eq (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    profile N = (headDimension N, 2 + headDimension N,
      headDimension N, 1, 4, 4 - headDimension N) := by
  have h := invariants N hRN hND
  unfold profile BinaryCarrierRadicalProfiles16T1332.profile
  rw [h.card_eq, inf_eq_left.mpr hND.le, h.normalHeadMax_eq,
    max_eq_right h.head_pos, h.radicalHead_eq, h.center_card, h.derived_card]
  simp only [Nat.log_pow (by decide : 1 < (2 : ℕ))]
  rfl

theorem normal_profile (N : Subgroup Original) [N.Normal] (hRN : R < N) (hND : N < D) :
    profile N = (1,3,1,1,4,3) ∨ profile N = (2,4,2,1,4,2) ∨
      profile N = (3,5,3,1,4,1) := by
  have hp := profile_eq N hRN hND
  rcases head_cases N hRN hND with h1 | h2 | h3
  · exact Or.inl (by simpa [h1] using hp)
  · exact Or.inr (Or.inl (by simpa [h2] using hp))
  · exact Or.inr (Or.inr (by simpa [h3] using hp))

end SymmetricSubgroupAsymptotics.BinaryCarrierStarIntermediate16T1332
