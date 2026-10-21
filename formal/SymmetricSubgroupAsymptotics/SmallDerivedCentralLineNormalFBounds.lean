import SymmetricSubgroupAsymptotics.DerivedFourNormalDenominators

/-! A derived subgroup of order at most four leaves only central order-two
denominators in a nonabelian quotient. Thus three small centre calculations
can cover an entire original normal lattice. No enumeration of that lattice
or assertion about the original central-derived intersection is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallDerivedCentralLineNormalFBounds
open MarkedC4.ActualNormalFMarkedPeel MarkedC4.RDTNormalFInterface

variable {G : Type} [Group G] [Finite G]

theorem nonabelian_derived_intersection_card_le_two
    (hderived : Nat.card (commutator G) ≤ 4)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    Nat.card (N ⊓ commutator G : Subgroup G) ≤ 2 := by
  let L := N ⊓ commutator G
  have hproper : L ≠ commutator G := by
    intro h
    have hle : commutator G ≤ N := by rw [← h]; exact inf_le_left
    letI : IsMulCommutative (G ⧸ N) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
    exact hnonab (fun a b => mul_comm' a b)
  have hlt : Nat.card L < Nat.card (commutator G) := by
    by_contra h
    exact hproper (Subgroup.eq_of_le_of_card_ge inf_le_right (by omega))
  have hdvd : Nat.card L ∣ Nat.card (commutator G) := by
    have h := (L.subgroupOf (commutator G)).card_subgroup_dvd_card
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show L ≤ commutator G from inf_le_right)).toEquiv] at h
  change Nat.card L ≤ 2
  by_contra h
  have hL : Nat.card L = 3 := by omega
  have hD : Nat.card (commutator G) = 4 := by omega
  norm_num only [hL, hD] at hdvd

/-- Every remaining denominator is an actual central line of the original
derived subgroup; its quotient estimate retains that very denominator. -/
theorem quotient_center_card_le
    (hderived : Nat.card (commutator G) ≤ 4)
    (hcenter : Nat.card (Subgroup.center G) ≤ 16)
    (hlines : ∀ (L : Subgroup G) [L.Normal], L ≤ commutator G →
      Nat.card L = 2 → Nat.card (Subgroup.center (G ⧸ L)) ≤ 16)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (G ⧸ N)) ≤ 16 := by
  let L := N ⊓ commutator G
  have h := quotient_center_card_le_derived_intersection N
  by_cases hb : L = ⊥
  · let e : G ⧸ L ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
    have hc := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
    exact (h.trans_eq hc).trans hcenter
  · have htwo : Nat.card L = 2 := by
      have hlo := L.one_lt_card_iff_ne_bot.mpr hb
      have hhi := nonabelian_derived_intersection_card_le_two hderived N hnonab
      change Nat.card L ≤ 2 at hhi
      omega
    exact h.trans (hlines L inf_le_right htwo)

theorem five_quarters_packet
    (hderived : Nat.card (commutator G) ≤ 4)
    (hcenter : Nat.card (Subgroup.center G) ≤ 16)
    (hlines : ∀ (L : Subgroup G) [L.Normal], L ≤ commutator G →
      Nat.card L = 2 → Nat.card (Subgroup.center (G ⧸ L)) ≤ 16)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    ∃ F : Subgroup (G ⧸ N), F.Normal ∧
      commutatorLog F + (5 / 4 : ℝ) * centralLog F ≤ 8 ∧
      centralLog F ≤ 4 := by
  have hd := (SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hderived
  have hz := quotient_center_card_le hderived hcenter hlines N hnonab
  have hlog (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2 ^ k) :
      Real.logb 2 (n : ℝ) ≤ k := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hn)).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using
      (show (n : ℝ) ≤ (2 ^ k : ℕ) by exact_mod_cast hk)
  have hdlog : commutatorLog (⊤ : Subgroup (G ⧸ N)) ≤ 2 := by
    change Real.logb 2 (Nat.card (commutator (G ⧸ N)) : ℝ) ≤ 2
    simpa only [Nat.cast_ofNat] using hlog _ 2 Nat.card_pos (by simpa using hd)
  have hzlog : centralLog (⊤ : Subgroup (G ⧸ N)) ≤ 4 := by
    simpa only [centralLog, targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] using hlog _ 4 Nat.card_pos (by simpa using hz)
  exact ⟨⊤, inferInstance, by linarith, hzlog⟩

end SymmetricSubgroupAsymptotics.SmallDerivedCentralLineNormalFBounds
