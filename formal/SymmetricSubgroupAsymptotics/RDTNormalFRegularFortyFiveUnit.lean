import SymmetricSubgroupAsymptotics.BinaryRegularEightSmallAxes
import SymmetricSubgroupAsymptotics.RDTNormalFRegularFortyFive
import SymmetricSubgroupAsymptotics.NormalFUnitTopCardBounds
import SymmetricSubgroupAsymptotics.DerivedQuotientSubgroupBound

/-! Every original rank-five regular-K45 action, with arbitrary affine
lifts and every original normal denominator. Small derived-intersection
axes use the existing joint linear envelope; large axes leave a quotient
of order at most64. No splitting or saturated derived-axis equality is
assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
open BinaryRegularEightNaturalRegistry

theorem regular45_rank_five_unit_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = H)
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K45)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have horder : Nat.card U = 1024 := F.regular45_original_card hH hK
  have hd : Nat.card (commutator U) ≤ 32 := by
    have ha : 32 ≤ Nat.card (Abelianization U) :=
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
        (pGroup_pow_genRank_le_abelianization_card 2 hU)
    have hc := (commutator U).card_eq_card_quotient_mul_card_subgroup
    change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hc
    rw [horder] at hc
    nlinarith
  let f := F.top.rangeRestrict
  let e : H ≃* F.top.range := (MulEquiv.subgroupCongr hH).symm
  have hpow (g : F.top.range) : g^2=1 := by
    apply e.symm.injective
    simpa only [map_pow,map_one] using
      BinaryEightTopAbelianizationCards.regular_pow_two (e.symm g)
  letI : IsMulCommutative F.top.range :=
    ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun g => orderOf_dvd_iff_pow_eq_one.mpr (hpow g)) a b).eq⟩⟩
  have hm : (commutator U).map f = ⊥ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr F.top.rangeRestrict_surjective]
    exact commutator_eq_bot F.top.range
  have hDker : commutator U ≤ F.top.ker := by
    intro u hu
    have hh : f u ∈ (commutator U).map f := ⟨u,hu,rfl⟩
    rw [hm] at hh
    exact congrArg Subtype.val (show f u = 1 from hh)
  let L := N ⊓ commutator U
  have hLker : L ≤ F.top.ker := inf_le_right.trans hDker
  have he : ∀ g v, rho g v = F.coordinateTopAction (e g) v := fun _ _ => rfl
  let A := F.sharedOriginalAxis rho e he L
  have hcoord : F.coordinateSubgroup A.toSubmodule = L := by
    change F.coordinateSubgroup (F.ambientAxis L) = L
    rw [F.coordinateSubgroup_ambientAxis,inf_eq_right.mpr hLker]
  have hAK : A.toSubmodule ≤ F.kernelSpace := F.ambientAxis_le_kernelSpace L
  have hAc : Nat.card A.toSubmodule = Nat.card L := by
    rw [← F.coordinateSubgroup_card A.toSubmodule hAK,hcoord]
  have hnonabL : ¬ ∀ a b : U ⧸ L, a*b=b*a := by
    intro hcomm
    let q : U ⧸ L →* U ⧸ N := QuotientGroup.lift L (QuotientGroup.mk' N) (by
      rw [QuotientGroup.ker_mk']; exact inf_le_left)
    apply hnonab
    intro a b
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective N b
    have hh := congrArg q (hcomm ((QuotientGroup.mk' L) x) ((QuotientGroup.mk' L) y))
    simpa only [map_mul] using hh
  by_cases hsmall : Module.finrank (ZMod 2) A.toSubmodule ≤ 3
  · have hAle := small_axis_le_R45 A hsmall
    have hchart : chart45.space = F.kernelSpace := kernel45_space.trans hK.symm
    have hc := F.shared_quotient_center_card_le rho e he chart45.space hchart
      A (hAK.trans_eq hchart.symm) 8
      (BinaryRegularFortyFiveAllDerivedAxes.coordinate_capacity A hAle hsmall)
    let eq : (U ⧸ F.coordinateSubgroup
        (F.sharedSubrepresentation rho e he A).toSubmodule) ≃* (U ⧸ L) :=
      QuotientGroup.quotientMulEquivOfEq hcoord
    have heq := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv eq).toEquiv
    have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 8 :=
      (quotient_center_card_le_derived_intersection N).trans (heq.symm.trans_le hc)
    exact normalF_unit_top_packet_of_card_bounds 5 3
      ((SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hd)
      (by simpa using hz) (by decide) (by decide)
  · have hdim : 4 ≤ Module.finrank (ZMod 2) A.toSubmodule := by omega
    have ha : 16 ≤ Nat.card L := by
      rw [←hAc, Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
    have hq : Nat.card (U ⧸ L) ≤ 64 := by
      have hc := L.card_eq_card_quotient_mul_card_subgroup
      rw [horder] at hc
      nlinarith
    have hzL : Nat.card (Subgroup.center (U ⧸ L)) ≤ 16 := by
      have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonabL
      have hc := (Subgroup.center (U ⧸ L)).card_mul_index
      nlinarith
    have hz := (quotient_center_card_le_derived_intersection N).trans hzL
    have hdq : Nat.card (commutator (U ⧸ N)) ≤ 2 := by
      exact quotient_derived_card_le_of_subgroup N L inf_le_left inf_le_right 2
        (by nlinarith)
    exact normalF_unit_top_packet_of_card_bounds 1 4
      (by simpa using hdq) (by simpa using hz) (by decide) (by decide)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
