import SymmetricSubgroupAsymptotics.DerivedThirtyTwoNormalFBound

/-! A unit packet from actual derived order at most1024. When the source
has derived order at most512, no small-denominator certificate is needed;
otherwise only original order-two derived denominators need a centre bound.
The SAME derived intersection pays both actual quotient factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance derivedOneThousandTwentyFourUnitPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {G : Type} [Group G] [Finite G]

theorem derived_one_thousand_twenty_four_unit_packet
    (hG : IsPGroup 2 G)
    (hderived : Nat.card (commutator G)≤1024)
    (hcenter : Nat.card (Subgroup.center G)≤32)
    (hquotcenter : ∀ N : Subgroup G,∀ [N.Normal],
      (¬∀ a b : G ⧸ N,a*b=b*a) → Nat.card (Subgroup.center (G ⧸ N))≤256)
    (hsmall : ∀ L : Subgroup G,∀ [L.Normal],L<commutator G →
      Nat.card L=2 → 512<Nat.card (commutator G) →
        Nat.card (Subgroup.center (G ⧸ L))≤128)
    (N : Subgroup G) [N.Normal] (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a) :
    ∃ F : Subgroup (G ⧸ N),F.Normal ∧
      commutatorLog F+centralLog F≤16 ∧ centralLog F≤8 := by
  let L := N⊓commutator G
  have hLproper : L<commutator G := by
    apply lt_of_le_of_ne inf_le_right
    intro he
    have hDN : commutator G≤N := by rw [←he];exact inf_le_left
    letI : IsMulCommutative (G ⧸ N) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hDN
    exact hnonab (fun a b => mul_comm' a b)
  have hd := quotient_derived_card_mul_intersection N
  change Nat.card L*Nat.card (commutator (G ⧸ N))=Nat.card (commutator G) at hd
  have hz := quotient_center_card_le_derived_intersection N
  change Nat.card (Subgroup.center (G ⧸ N))≤Nat.card (Subgroup.center (G ⧸ L)) at hz
  have hz256 := hquotcenter N hnonab
  have hb : Nat.card (commutator (G ⧸ N))*Nat.card (Subgroup.center (G ⧸ N))≤2^16 := by
    by_cases hL : L=⊥
    · let e : G ⧸ L ≃* G :=
        (QuotientGroup.quotientMulEquivOfEq hL).trans QuotientGroup.quotientBot
      have he := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
      have hz32 : Nat.card (Subgroup.center (G ⧸ N))≤32 := (hz.trans_eq he).trans hcenter
      have hd1024 : Nat.card (commutator (G ⧸ N))≤1024 :=
        (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hderived
      exact (Nat.mul_le_mul hd1024 hz32).trans (by norm_num)
    · have htwo : 2≤Nat.card L := L.one_lt_card_iff_ne_bot.mpr hL
      by_cases hd512 : Nat.card (commutator G)≤512
      · have hq256 : Nat.card (commutator (G ⧸ N))≤256 := by nlinarith
        exact (Nat.mul_le_mul hq256 hz256).trans (by norm_num)
      · obtain ⟨k,hk⟩ := (hG.to_subgroup L).exists_card_eq
        by_cases hklow : k≤1
        · have hcases : Nat.card L=2 := by
            have hkpos : 1≤k := by
              by_contra hh
              have he : k=0 := by omega
              have hc : Nat.card L=1 := hk.trans (by rw [he,pow_zero])
              omega
            have he : k=1 := by omega
            exact hk.trans (by rw [he];norm_num)
          have hz128 := hz.trans (hsmall L hLproper hcases (by omega))
          have hd512 : Nat.card (commutator (G ⧸ N))≤512 := by nlinarith
          exact (Nat.mul_le_mul hd512 hz128).trans (by norm_num)
        · have hlarge : 4≤Nat.card L := by
            have hp := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega : 2≤k)
            simpa only [←hk] using hp
          have hq256 : Nat.card (commutator (G ⧸ N))≤256 := by nlinarith
          exact (Nat.mul_le_mul hq256 hz256).trans (by norm_num)
  have hp := normalF_unit_packet_of_actual_product_bound
    (⊤ : Subgroup (G ⧸ N)) 16 8 (by
      simpa only [targetCommutator,commutator_def,targetCentralizer,
        Subgroup.coe_top,Subgroup.centralizer_univ] using hb) (by
      simpa only [targetCentralizer,Subgroup.coe_top,Subgroup.centralizer_univ] using hz256)
  exact ⟨⊤,inferInstance,hp⟩
end SymmetricSubgroupAsymptotics
