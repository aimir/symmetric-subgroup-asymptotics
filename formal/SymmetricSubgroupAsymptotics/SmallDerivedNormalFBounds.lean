import SymmetricSubgroupAsymptotics.DerivedIntersectionQuotientCenter
import SymmetricSubgroupAsymptotics.SmallBinaryNormalFBounds

/-! A nonabelian quotient of a group whose derived group has order at most
two cannot kill any derived element. Consequently its centre is no larger
than the original centre. This treats every literal normal denominator at
once, without a normal-subgroup census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {G : Type} [Group G] [Finite G]

theorem derived_intersection_eq_bot
    (hderived : Nat.card (commutator G) ≤ 2)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    N ⊓ commutator G = ⊥ := by
  by_contra hnot
  have htwo : 2 ≤ Nat.card (N ⊓ commutator G : Subgroup G) :=
    (N ⊓ commutator G).one_lt_card_iff_ne_bot.mpr hnot
  have heq : N ⊓ commutator G = commutator G :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (hderived.trans htwo)
  have hle : commutator G ≤ N := by
    rw [← heq]
    exact inf_le_left
  letI : IsMulCommutative (G ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
  exact hnonab (fun a b => mul_comm' a b)

theorem quotient_center_card_le
    (hderived : Nat.card (commutator G) ≤ 2)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (G ⧸ N)) ≤ Nat.card (Subgroup.center G) := by
  have h := quotient_center_card_le_derived_intersection N
  let e : G ⧸ (N ⊓ commutator G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq (derived_intersection_eq_bot hderived N hnonab)).trans
      QuotientGroup.quotientBot
  have he := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv
    e).toEquiv
  exact h.trans_eq he

theorem quotient_derived_card_le
    (N : Subgroup G) [N.Normal] :
    Nat.card (commutator (G ⧸ N)) ≤ Nat.card (commutator G) := by
  let q := QuotientGroup.mk' N
  have hm : (commutator G).map q = commutator (G ⧸ N) := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    rfl
  rw [← hm]
  exact Nat.card_le_card_of_surjective (q.subgroupMap (commutator G))
    (q.subgroupMap_surjective (commutator G))

/-- The actual whole quotient works uniformly with coefficient5/4 once
the original centre has order at most8 and the original derived group has
order at most2. Both bounds concern the original source. -/
theorem five_quarters_packet
    (hderived : Nat.card (commutator G) ≤ 2)
    (hcenter : Nat.card (Subgroup.center G) ≤ 8)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    ∃ F : Subgroup (G ⧸ N), F.Normal ∧
      commutatorLog F + (5 / 4 : ℝ) * centralLog F ≤ 8 ∧
      centralLog F ≤ 4 := by
  have hd : Nat.card (commutator (G ⧸ N)) ≤ 2 :=
    (quotient_derived_card_le N).trans hderived
  have hz : Nat.card (Subgroup.center (G ⧸ N)) ≤ 8 :=
    (quotient_center_card_le hderived N hnonab).trans hcenter
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdlog : commutatorLog (⊤ : Subgroup (G ⧸ N)) ≤ 1 := by
    change Real.logb 2 (Nat.card (commutator (G ⧸ N)) : ℝ) ≤ 1
    simpa only [Nat.cast_one] using
      hlog (Nat.card (commutator (G ⧸ N))) 1 Nat.card_pos (by simpa using hd)
  have hzlog : centralLog (⊤ : Subgroup (G ⧸ N)) ≤ 3 := by
    simpa only [centralLog, targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] using
        hlog _ 3 Nat.card_pos (by simpa using hz)
  exact ⟨⊤, inferInstance, by linarith, by linarith⟩

/-- The same argument covers every rank-six sixteen-point source of
order at most128, including arbitrary original normal quotients. -/
theorem sixteen_rank_six_small_order_packet
    {X : Type} [Finite X] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X]
    (hG : IsPGroup 2 G) (hdegree : Nat.card X = 16)
    (hcard : Nat.card G ≤ 128) (hrank : 6 ≤ MarkedC4.genRank G)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    ∃ F : Subgroup (G ⧸ N), F.Normal ∧
      commutatorLog F + (5 / 4 : ℝ) * centralLog F ≤ 8 ∧
      centralLog F ≤ 4 := by
  have hd : Nat.card (commutator G) ≤ 2 := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : 64 ≤ 2 ^ MarkedC4.genRank G :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank
    have hab := pGroup_pow_genRank_le_abelianization_card 2 hG
    have hf := (commutator G).card_eq_card_quotient_mul_card_subgroup
    change Nat.card G = Nat.card (Abelianization G) * Nat.card (commutator G) at hf
    nlinarith
  have hnonabG : ¬ ∀ a b : G, a * b = b * a := by
    intro hcomm
    apply hnonab
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    simpa only [map_mul] using congrArg (QuotientGroup.mk' N) (hcomm x y)
  have hx : Nonempty X :=
    (Nat.card_pos_iff.mp (by rw [hdegree]; decide : 0 < Nat.card X)).1
  obtain ⟨x⟩ := hx
  have hzlt := transitive_nonabelian_center_card_lt x hnonabG
  rw [hdegree] at hzlt
  obtain ⟨k, hk⟩ := (hG.to_subgroup (Subgroup.center G)).exists_card_eq
  have hk3 : k ≤ 3 := by
    by_contra hnot
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 4 ≤ k)
    rw [hk] at hzlt
    norm_num at hp
    omega
  have hz : Nat.card (Subgroup.center G) ≤ 8 := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk3
  exact five_quarters_packet hd hz N hnonab

end SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds
