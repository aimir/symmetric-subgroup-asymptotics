import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds

/-! A derived group of order at most four with central part of order at
most two has only two possible proper original normal denominators. This
reduces all nonabelian quotient-centre bounds to the original group and
its one central-derived quotient, rather than a full normal census. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.DerivedFourNormalDenominators

private theorem aut_fixes_of_card_le_two
    {A : Type} [Group A] [Finite A]
    (hcard : Nat.card A ≤ 2) (f : MulAut A) (x : A) : f x = x := by
  by_cases hx : x = 1
  · simpa only [hx, map_one]
  by_contra hfx
  have hf1 : f x ≠ 1 := by
    intro h
    apply hx
    apply f.injective
    simpa only [map_one] using h
  letI : Fintype A := Fintype.ofFinite A
  have hthree : 3 ≤ Nat.card A := by
    rw [Nat.card_eq_fintype_card]
    calc
      3 = ({1, x, f x} : Finset A).card := by
        simp [hx, hf1, hfx, Ne.symm hx, Ne.symm hf1, Ne.symm hfx]
      _ ≤ Fintype.card A := Finset.card_le_univ _
  omega

theorem normal_card_le_two_le_center
    {G : Type} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (hcard : Nat.card H ≤ 2) :
    H ≤ Subgroup.center G := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  have he := aut_fixes_of_card_le_two hcard (MulAut.conjNormal g) (⟨x, hx⟩ : H)
  have hh := congrArg (fun z : H => z.val) he
  change g * x * g⁻¹ = x at hh
  have ht := congrArg (fun z : G => z * g) hh
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using ht

theorem intersection_cases
    {G : Type} [Group G] [Finite G]
    (hderived : Nat.card (commutator G) ≤ 4)
    (hcentral : Nat.card (commutator G ⊓ Subgroup.center G : Subgroup G) ≤ 2)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    N ⊓ commutator G = ⊥ ∨
      N ⊓ commutator G = commutator G ⊓ Subgroup.center G := by
  let L := N ⊓ commutator G
  have hproper : L ≠ commutator G := by
    intro heq
    have hle : commutator G ≤ N := by rw [← heq]; exact inf_le_left
    letI : IsMulCommutative (G ⧸ N) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
    exact hnonab (fun a b => mul_comm' a b)
  have hlt : Nat.card L < Nat.card (commutator G) := by
    by_contra hnot
    exact hproper (Subgroup.eq_of_le_of_card_ge inf_le_right (by omega))
  have hsmall : Nat.card L ≤ 2 := by
    have hdvd : Nat.card L ∣ Nat.card (commutator G) := by
      have h := (L.subgroupOf (commutator G)).card_subgroup_dvd_card
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show L ≤ commutator G from inf_le_right)).toEquiv] at h
    by_contra hnot
    have hL : Nat.card L = 3 := by omega
    have hD : Nat.card (commutator G) = 4 := by omega
    norm_num only [hL, hD] at hdvd
  have hle : L ≤ commutator G ⊓ Subgroup.center G :=
    le_inf inf_le_right (normal_card_le_two_le_center L hsmall)
  by_cases hb : L = ⊥
  · exact Or.inl hb
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle
      (hcentral.trans (L.one_lt_card_iff_ne_bot.mpr hb)))

theorem quotient_center_card_le_max
    {G : Type} [Group G] [Finite G]
    (hderived : Nat.card (commutator G) ≤ 4)
    (hcentral : Nat.card (commutator G ⊓ Subgroup.center G : Subgroup G) ≤ 2)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ a b : G ⧸ N, a * b = b * a) :
    Nat.card (Subgroup.center (G ⧸ N)) ≤
      max (Nat.card (Subgroup.center G))
        (Nat.card (Subgroup.center (G ⧸ (commutator G ⊓ Subgroup.center G)))) := by
  have h := quotient_center_card_le_derived_intersection N
  rcases intersection_cases hderived hcentral N hnonab with hbot | hcentralEq
  · let e : G ⧸ (N ⊓ commutator G) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    have hc := Nat.card_congr
      (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
    exact (h.trans_eq hc).trans (le_max_left _ _)
  · let e := QuotientGroup.quotientMulEquivOfEq hcentralEq
    have hc := Nat.card_congr
      (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv
    exact (h.trans_eq hc).trans (le_max_right _ _)

end SymmetricSubgroupAsymptotics.DerivedFourNormalDenominators
