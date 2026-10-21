import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds
import SymmetricSubgroupAsymptotics.DerivedQuotientExactCard
import SymmetricSubgroupAsymptotics.NormalFPacketOfActualProduct

/-! A joint capacity for the actual proper derived intersections supplies
all nonabelian quotient packets. The same original intersection pays the
quotient-derived order and the quotient-centre order simultaneously. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface
variable {G : Type} [Group G] [Finite G]

/-- This intermediate theorem exposes the finite geometric capacity to
be proved by the original chart. It introduces no published input. -/
theorem derived_thirty_two_normalF_packet
    (hderived : Nat.card (commutator G)=32)
    (hcenter : Nat.card (Subgroup.center G)≤32)
    (hcapacity : ∀ L : Subgroup G, ∀ [L.Normal],
      L≠⊥ → L<commutator G →
      Nat.card L*Nat.card (Subgroup.center (G ⧸ L))≤512)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N,a*b=b*a) :
    ∃ F : Subgroup (G ⧸ N), F.Normal ∧
      commutatorLog F+(5/4 : ℝ)*centralLog F≤16 ∧ centralLog F≤8 := by
  let L := N ⊓ commutator G
  have hLproper : L<commutator G := by
    apply lt_of_le_of_ne inf_le_right
    intro he
    have hDN : commutator G≤N := by rw [←he];exact inf_le_left
    letI : IsMulCommutative (G ⧸ N) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hDN
    exact hnonab (fun a b => mul_comm' a b)
  have hd := quotient_derived_card_mul_intersection N
  change Nat.card L*Nat.card (commutator (G ⧸ N))=Nat.card (commutator G) at hd
  rw [hderived] at hd
  have hz := quotient_center_card_le_derived_intersection N
  change Nat.card (Subgroup.center (G ⧸ N))≤Nat.card (Subgroup.center (G ⧸ L)) at hz
  have hb :
      Nat.card (commutator (G ⧸ N))^4*Nat.card (Subgroup.center (G ⧸ N))^5≤2^(4*16) ∧
      Nat.card (Subgroup.center (G ⧸ N))≤2^8 := by
    by_cases hL : L=⊥
    · let e : G ⧸ L ≃* G :=
        (QuotientGroup.quotientMulEquivOfEq hL).trans QuotientGroup.quotientBot
      have he := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
      have hz32 : Nat.card (Subgroup.center (G ⧸ N))≤32 :=
        (hz.trans_eq he).trans hcenter
      have hd32 : Nat.card (commutator (G ⧸ N))≤32 :=
        (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hderived.le
      constructor
      · exact (Nat.mul_le_mul (Nat.pow_le_pow_left hd32 4)
          (Nat.pow_le_pow_left hz32 5)).trans (by norm_num)
      · exact hz32.trans (by norm_num)
    · have htwo : 2≤Nat.card L := L.one_lt_card_iff_ne_bot.mpr hL
      have hc := hcapacity L hL hLproper
      have hd16 : Nat.card (commutator (G ⧸ N))≤16 := by nlinarith
      have hz256 : Nat.card (Subgroup.center (G ⧸ N))≤256 := by nlinarith
      constructor
      · exact (Nat.mul_le_mul (Nat.pow_le_pow_left hd16 4)
          (Nat.pow_le_pow_left hz256 5)).trans (by norm_num)
      · exact hz256
  have hp := normalF_fiveQuarter_packet_of_actual_product_bound
    (⊤ : Subgroup (G ⧸ N)) 16 8 (by
      simpa only [targetCommutator,commutator_def,targetCentralizer,
        Subgroup.coe_top,Subgroup.centralizer_univ] using hb.1) (by
      simpa only [targetCentralizer,Subgroup.coe_top,Subgroup.centralizer_univ] using hb.2)
  exact ⟨⊤,inferInstance,hp⟩

end SymmetricSubgroupAsymptotics
