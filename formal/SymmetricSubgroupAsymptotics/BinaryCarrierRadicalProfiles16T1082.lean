import SymmetricSubgroupAsymptotics.PrimeDerivedOrderTwoProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1082

/-! Every original normal inside the actual order-two relative radical
of 16T1082 has one of two exact profiles. The whole original group,
its conjugation action and its quotient groups are retained. No new
finite table or normal-subgroup enumeration is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
private abbrev hker := BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator

private theorem derived_card : Nat.card D = 2 ^ 4 :=
  BinaryCarrierDerivedOrder16T1082.card_commutator

private theorem radical_card : Nat.card R = 2 :=
  BinaryCarrierDerivedRadical16T1082.card_relative_radical

theorem radical_le_center : R ≤ Subgroup.center Original :=
  NormalOrderTwo.le_center R radical_card

theorem relativeRadical_eq_bot : primeRelativeRadical 2 R = ⊥ :=
  NormalOrderTwo.relativeRadical_eq_bot R radical_card

theorem relativeHead_eq_one :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 R) = 1 :=
  NormalOrderTwo.relativeHead_eq_one R radical_card

theorem normalHeadMax_eq_one : primeNormalHeadMax 2 R = 1 :=
  NormalOrderTwo.normalHeadMax_eq_one R radical_card

theorem normal_cases (M : Subgroup Original) (hM : M ≤ R) : M = ⊥ ∨ M = R :=
  NormalOrderTwo.subgroup_cases R radical_card M hM

theorem centerPreimage_bot_eq_radical :
    quotientCenterPreimage (⊥ : Subgroup Original) = R :=
  PrimeDerivedOrderTwoProfiles.centerPreimage_bot_eq_radical
    4 derived_card radical_card (by decide) hker
    BinaryCarrierFormTransport16T1082.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierRadicalSaturation16T1082.certificate
    BinaryCarrierRadicalSaturation16T1082.nonempty_words

theorem centerPreimage_radical_eq_derived : quotientCenterPreimage R = D :=
  PrimeDerivedOrderTwoProfiles.centerPreimage_radical_eq_derived
    4 derived_card radical_card (by decide) hker
    BinaryCarrierFormTransport16T1082.actual_form_ker_inf_eq_bot_of_independent

abbrev profile (M : Subgroup Original) [M.Normal] :=
  PrimeDerivedOrderTwoProfiles.profile M

/-- Universal exact profile alternatives for original normal axes inside
R; neither an axis enumeration nor a statement about their weights. -/
theorem normal_profile (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    profile M = (0,0,0,0,1,4) ∨ profile M = (1,1,1,0,3,3) :=
  PrimeDerivedOrderTwoProfiles.normal_profile
    4 derived_card radical_card (by decide) hker
    BinaryCarrierFormTransport16T1082.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierRadicalSaturation16T1082.certificate
    BinaryCarrierRadicalSaturation16T1082.nonempty_words M hM

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalProfiles16T1082

