import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalHeisenbergProperClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalRankOneProperClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalTwistedProperClassGap

/-! A literal model-equivalence profile for the six exceptional families
paid by their proved order/index packets. Tits and sporadic models are
not included. No class-capacity inequality is part of this profile. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalProperClassProfile

def Profile (S : Type) [Group S] : Prop :=
  (∃ q : CFSG.PrimePower, Nonempty (S ≃* CFSG.Models.F4 q)) ∨
  (∃ q : CFSG.PrimePower, Nonempty (S ≃* CFSG.Models.TwistedE6 q)) ∨
  (∃ q : CFSG.PrimePower, Nonempty (S ≃* CFSG.Models.TrialityD4 q)) ∨
  (∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* CFSG.Models.Suzuki m)) ∨
  (∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* CFSG.Models.ReeG2 m)) ∨
  (∃ m : ℕ, 0 < m ∧ Nonempty (S ≃* CFSG.Models.ReeF4 m))

end SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalProperClassProfile

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_exceptional_profile
    (D : NonaffineData G X)
    (hmodel : PrimitiveSocleExceptionalProperClassProfile.Profile D.Simple)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  rcases hmodel with hf4 | he6 | htriality | hsuzuki | hree | hree4
  · obtain ⟨q,⟨e⟩⟩ := hf4
    exact D.proper_subnormal_class_cube_le_of_fFour_all_fields q e H hH hne
  · obtain ⟨q,⟨e⟩⟩ := he6
    exact D.proper_subnormal_class_cube_le_of_twistedE6_all_fields q e H hH hne
  · obtain ⟨q,⟨e⟩⟩ := htriality
    exact D.proper_subnormal_class_cube_le_of_triality_all_fields q e H hH hne
  · obtain ⟨m,hm,⟨e⟩⟩ := hsuzuki
    exact D.proper_subnormal_class_cube_le_of_suzuki_all_parameters m hm e H hH hne
  · obtain ⟨m,hm,⟨e⟩⟩ := hree
    exact D.proper_subnormal_class_cube_le_of_reeGTwo_all_parameters m hm e H hH hne
  · obtain ⟨m,hm,⟨e⟩⟩ := hree4
    exact D.proper_subnormal_class_cube_le_of_reeFFour_positive_parameters m hm e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
