import SymmetricSubgroupAsymptotics.RDTNormalFRegularFortyFiveUnit

/-! One installer for all regular-eight kernels of dimensions five and
six. Only the small invariant denominator's linear centre envelope varies;
large denominators leave an actual quotient of order at most64. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
open BinaryRegularEightNaturalRegistry

theorem regular_middle_kernel_unit_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = H)
    (k : ℕ) (hk : 5 ≤ k ∧ k ≤ 6) (K : BinaryCoordinateSpace 8 k)
    (hK : K.space = F.kernelSpace)
    (henvelope : ∀ A : Subrepresentation rho,
      Module.finrank (ZMod 2) A.toSubmodule ≤ k-4 →
      A.toSubmodule = ⊥ ∨
      Nat.card {v : V // v ∈ K.space ∧ ∀ t : H, rho t v-v ∈ A.toSubmodule} *
        Nat.card {t : H // ∀ v, v ∈ K.space → rho t v-v ∈ A.toSubmodule} ≤
          16 * Nat.card A.toSubmodule)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  have horder : Nat.card U = 8 * 2^k := by
    have ht : Nat.card F.top.range = 8 :=
      (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
    have hc := F.kernelSpace_card_mul_top
    rw [←hK,K.card,ht] at hc
    omega
  have horderSmall : Nat.card U ≤ 512 := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk.2
    norm_num at hp
    nlinarith [horder]
  have hd : Nat.card (commutator U) ≤ 16 := by
    have ha : 32 ≤ Nat.card (Abelianization U) :=
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
        (pGroup_pow_genRank_le_abelianization_card 2 hU)
    have hc := (commutator U).card_eq_card_quotient_mul_card_subgroup
    change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hc
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
  have hz : Nat.card (Subgroup.center (U ⧸ N)) ≤ 16 := by
    apply (quotient_center_card_le_derived_intersection N).trans
    by_cases hsmall : Module.finrank (ZMod 2) A.toSubmodule ≤ k-4
    · rcases henvelope A hsmall with hzero | hcapacity
      · have hLbot : L = ⊥ := L.eq_bot_of_card_eq (by
          rw [←hAc,hzero,Module.natCard_eq_pow_finrank (K := ZMod 2)]
          simp)
        let eq : U ⧸ L ≃* U :=
          (QuotientGroup.quotientMulEquivOfEq hLbot).trans QuotientGroup.quotientBot
        have hnG : ¬ ∀ a b : U, a*b=b*a := by
          intro hcomm
          apply hnonabL
          intro a b
          apply eq.injective
          simpa only [map_mul] using hcomm (eq a) (eq b)
        have hdegree : Nat.card X = 16 := by
          simpa only [Nat.card_fin] using F.card_points
        obtain ⟨x⟩ := (Nat.card_pos_iff.mp (by rw [hdegree]; decide : 0 < Nat.card X)).1
        have hcent := (transitive_nonabelian_center_card_lt x hnG).le
        rw [hdegree] at hcent
        rwa [Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv eq).toEquiv]
      · have hc := F.shared_quotient_center_card_le rho e he K.space hK
          A (hAK.trans_eq hK.symm) 16 hcapacity
        let eq : (U ⧸ F.coordinateSubgroup
            (F.sharedSubrepresentation rho e he A).toSubmodule) ≃* (U ⧸ L) :=
          QuotientGroup.quotientMulEquivOfEq hcoord
        have heq := Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv eq).toEquiv
        exact heq.symm.trans_le hc
    · have hdim : k-3 ≤ Module.finrank (ZMod 2) A.toSubmodule := by omega
      have ha : 2^(k-3) ≤ Nat.card L := by
        rw [←hAc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hdim
      have hq : Nat.card (U ⧸ L) ≤ 64 := by
        have hc := L.card_eq_card_quotient_mul_card_subgroup
        rcases (by omega : k=5 ∨ k=6) with rfl | rfl <;> norm_num at ha horder <;> nlinarith
      have hi := SmallBinaryNormalFBounds.nonabelian_center_index_four_le hnonabL
      have hc := (Subgroup.center (U ⧸ L)).card_mul_index
      nlinarith
  exact normalF_unit_top_packet_of_card_bounds 4 4
    ((SmallDerivedNormalFBounds.quotient_derived_card_le N).trans hd)
    (by simpa using hz) (by decide) (by decide)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
