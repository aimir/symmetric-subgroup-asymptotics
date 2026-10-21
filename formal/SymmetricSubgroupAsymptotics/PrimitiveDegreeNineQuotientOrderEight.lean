import SymmetricSubgroupAsymptotics.DegreeNineTransitiveNormalQuotient
import SymmetricSubgroupAsymptotics.PrimitiveSmallSocleSingleFactor
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderRoundingGap

/-! Ordinary retained simple-index bounds and the actual regular Sylow
normalizer exclude the last quotient order nine in degree nine. The actual
socle quotient therefore has order at most eight, without any C336 row. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

theorem NonaffineData.degreeNine_quotient_card_le_eight
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 9)]
    [FaithfulSMul G (Fin 9)] (D : NonaffineData G (Fin 9))
    (hindex : PublishedSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 8 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by simp)
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  have hpow := quotientOrder_twoPow_le_cube_of_log (by omega) hlog
  have he' : ell ≤ 9 := by simpa only [Nat.card_fin] using he
  have hcube : 2 ^ Nat.card (G ⧸ finiteGroupSocle G) ≤ 729 :=
    hpow.trans (Nat.pow_le_pow_left he' 3)
  have hten : Nat.card (G ⧸ finiteGroupSocle G) < 10 := by
    by_contra h
    have hlo : 10 ≤ Nat.card (G ⧸ finiteGroupSocle G) := by omega
    have hbad : 1024 ≤ 729 := calc
      1024 = 2 ^ 10 := by decide
      _ ≤ 2 ^ Nat.card (G ⧸ finiteGroupSocle G) :=
        pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlo
      _ ≤ 729 := hcube
    omega
  letI : MulAction.IsPretransitive (finiteGroupSocle G) (Fin 9) := D.socle_transitive
  have hne := ninePoint_normal_transitive_quotient_card_ne_nine (finiteGroupSocle G)
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
