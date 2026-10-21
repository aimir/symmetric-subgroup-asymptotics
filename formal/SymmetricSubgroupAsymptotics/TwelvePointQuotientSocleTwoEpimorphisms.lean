import SymmetricSubgroupAsymptotics.PrimitiveTwelveActualQuotientEpimorphisms
import SymmetricSubgroupAsymptotics.CyclicByCyclicNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Actual twelve-point groups whose original normal quotients have socle
capacity two admit the same slope5/3 envelope used by the primitive branch.
This is a generic implication on actual quotients, not a classification
premise. The cyclic-by-cyclic corollary proves its capacity hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TwelvePointQuotientSocleTwoEpimorphisms
open Non2UnipotentPrefixFiniteMenu PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 12)]
    [FaithfulSMul G (Fin 12)]

theorem quotient_epi_le
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hSocle : ∀ (M : Subgroup G) [M.Normal], SocleNormalGeneratorBound (G ⧸ M) 2)
    (M : Subgroup G) [M.Normal] (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ M)) : ℝ) ≤
      (2 : ℝ)^(841 : ℕ) * (2 : ℝ)^((5/3 : ℝ)*(b : ℝ)) := by
  have he := (hZmud.generalCertificate (hSocle M)).envelope lit b J
  simp only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope, Nat.cast_ofNat] at he
  have horder : Nat.card (G ⧸ M) ≤ 2^29 :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' M)
      (QuotientGroup.mk'_surjective M)).trans (degreeTwelve_group_order_le (G := G))
  have haut : (Nat.card ((G ⧸ M) ≃* (G ⧸ M)) : ℝ) ≤ (2 : ℝ)^(841 : ℕ) := by
    exact_mod_cast mulEquiv_card_le_two_pow_sq_of_order 29 horder
  have hlog : 2 * (Real.logb 2 5 / 3) ≤ (5/3 : ℝ) := by
    have h := logb_two_five_div_five_lt_seven_fifteenths
    linarith
  have hp : (2 : ℝ)^((2 * (Real.logb 2 5 / 3))*(b : ℝ)) ≤
      (2 : ℝ)^((5/3 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg b))
  exact he.trans (mul_le_mul haut hp (by positivity) (by positivity))

omit [MulAction G (Fin 12)] [FaithfulSMul G (Fin 12)] in
/-- A cyclic normal kernel and cyclic actual quotient give two ambient
normal generators for every original normal subgroup, without splitting. -/
theorem cyclicByCyclic_quotient_socle_two
    (E : Subgroup G) [E.Normal] [IsCyclic E] [IsCyclic (G ⧸ E)]
    (M : Subgroup G) [M.Normal] : SocleNormalGeneratorBound (G ⧸ M) 2 := by
  apply quotientSocleNormalGeneratorBound_of_normalGen_le _ M
  intro H hH
  letI : H.Normal := hH
  exact CyclicByCyclicNormalGenerators.normalGen_le_two E H

end SymmetricSubgroupAsymptotics.TwelvePointQuotientSocleTwoEpimorphisms
