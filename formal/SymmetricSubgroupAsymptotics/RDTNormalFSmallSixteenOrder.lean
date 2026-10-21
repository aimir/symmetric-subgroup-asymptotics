import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds

/-! A uniform all-normal packet for EVERY rank-five sixteen-point binary
source of order at most128. A nontrivial normal denominator leaves a
quotient of order at most64; the trivial denominator retains the original
faithful transitive centre bound. No source or normal catalogue is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RDTNormalFSmallSixteenOrder
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface

theorem top_packet_of_card_bounds
    {Q : Type} [Group Q] [Finite Q]
    (hderived : Nat.card (commutator Q) ≤ 4)
    (hcenter : Nat.card (Subgroup.center Q) ≤ 16) :
    ∃ F : Subgroup Q, F.Normal ∧
      commutatorLog F + (5 / 4 : ℝ) * centralLog F ≤ 8 ∧ centralLog F ≤ 4 := by
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdlog : commutatorLog (⊤ : Subgroup Q) ≤ 2 := by
    change Real.logb 2 (Nat.card (commutator Q) : ℝ) ≤ 2
    simpa only [Nat.cast_ofNat] using hlog _ 2 Nat.card_pos (by simpa using hderived)
  have hzlog : centralLog (⊤ : Subgroup Q) ≤ 4 := by
    simpa only [centralLog, targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] using hlog _ 4 Nat.card_pos (by simpa using hcenter)
  exact ⟨⊤, inferInstance, by linarith, hzlog⟩

theorem all_nonabelian_quotients
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hdegree : Nat.card X = 16)
    (hcard : Nat.card G ≤ 128) (hrank : 5 ≤ MarkedC4.genRank G)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    ∃ F : Subgroup (G ⧸ N), F.Normal ∧
      commutatorLog F + (5 / 4 : ℝ) * centralLog F ≤ 8 ∧ centralLog F ≤ 4 := by
  have hd : Nat.card (commutator G) ≤ 4 := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : 32 ≤ 2 ^ MarkedC4.genRank G :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank
    have hab := pGroup_pow_genRank_le_abelianization_card 2 hG
    have hf := (commutator G).card_eq_card_quotient_mul_card_subgroup
    change Nat.card G = Nat.card (Abelianization G) * Nat.card (commutator G) at hf
    nlinarith
  have hz : Nat.card (Subgroup.center (G ⧸ N)) ≤ 16 := by
    by_cases hb : N = ⊥
    · let e : G ⧸ N ≃* G :=
        (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
      have hc := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
      rw [hc]
      have hnonabG : ¬ ∀ a b : G, a * b = b * a := by
        intro h
        apply hnonab
        intro a b
        apply e.injective
        simpa only [map_mul] using h (e a) (e b)
      obtain ⟨x⟩ := (Nat.card_pos_iff.mp (by rw [hdegree]; decide : 0 < Nat.card X)).1
      have h := transitive_nonabelian_center_card_lt x hnonabG
      rw [hdegree] at h
      omega
    · have hN : 2 ≤ Nat.card N := N.one_lt_card_iff_ne_bot.mpr hb
      have hf := N.card_eq_card_quotient_mul_card_subgroup
      have hq : Nat.card (G ⧸ N) ≤ 64 := by nlinarith
      have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonab
      have hc := (Subgroup.center (G ⧸ N)).card_mul_index
      nlinarith
  exact top_packet_of_card_bounds
    ((SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hd) hz

end SymmetricSubgroupAsymptotics.RDTNormalFSmallSixteenOrder
