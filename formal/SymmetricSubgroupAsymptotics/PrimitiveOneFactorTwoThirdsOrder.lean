import SymmetricSubgroupAsymptotics.PrimitiveCompositionTwoThirdsReceipt
import SymmetricSubgroupAsymptotics.PrimitiveSmallBinaryNonaffineQuotient
import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart
import SymmetricSubgroupAsymptotics.SimpleSocleQuotientOrderBudget

/-! The actual one-factor socle quotient fits two thirds of the original
primitive degree. The proof uses two actual order matches in the SAME retained
composition correspondence, actual binary action charts, and the unchanged
ordinary simple-index input. It does not claim the stronger half-degree bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem two_pow_le_cube_of_log {q ell : ℕ} (hell : 0<ell)
    (hq : (q : ℝ)≤3*Real.logb 2 ell) : 2^q≤ell^3 := by
  have hq' : (q : ℝ)≤Real.logb 2 ((ell : ℝ)^3) := by
    simpa only [Real.logb_pow] using hq
  have hp := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ)<2)
    (pow_pos (by exact_mod_cast hell) 3)).mp hq'
  rw [Real.rpow_natCast] at hp
  exact_mod_cast hp

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

theorem NonaffineData.oneFactor_twoThirds_quotient_bound_under_thirty
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hindex : PublishedSimpleIndexBounds)
    (hf : 5≤Nat.card X) (hs : Nat.card X<30) :
    3*Nat.card (G⧸finiteGroupSocle G)≤2*Nat.card X := by
  obtain ⟨M⟩ := catalogue G X (by omega)
  by_cases hm : (primitiveCompositionBoundRow M.row).kind=.orderBound
  · obtain ⟨ell,hell,hfive,helln,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
    have hq : Nat.card (G⧸finiteGroupSocle G)<15 :=
      quotient_order_lt_fifteen_of_log (by omega) (by omega) hlog
    obtain ⟨H,_,hi,⟨T⟩⟩ := compositionMatch_at_leastIndex
      catalogue D.noncommutative hell (by omega)
    have ht : (primitiveCompositionBoundRow T.row).degree=ell :=
      T.degree_eq.trans (H.index_eq_card.symm.trans hi)
    have hcard : Nat.card (finiteGroupSocle G)=Nat.card D.Simple :=
      Nat.card_congr (D.oneFactorEquiv hk).toEquiv
    have hfactor : Nat.card (G⧸finiteGroupSocle G)*Nat.card D.Simple=Nat.card G := by
      rw [←hcard]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)).symm
    letI : MulAction.IsPretransitive (finiteGroupSocle G) X := D.socle_transitive
    have hd : Nat.card X∣Nat.card D.Simple := by
      rw [←hcard]
      exact degree_dvd_card_of_transitive_normal (X := X) (finiteGroupSocle G)
    have hp := two_pow_le_cube_of_log (by omega) hlog
    have hr := primitiveComposition_twoAction_twoThirds_receipt M.row T.row
      ⟨Nat.card (G⧸finiteGroupSocle G),hq⟩ Nat.card_pos hm
      (by rwa [M.degree_eq]) (by rwa [M.degree_eq])
      (by rwa [ht]) (by rwa [ht,M.degree_eq])
      (by rw [←T.card_eq_row,←M.card_eq_row]; exact hfactor)
      (by rw [M.degree_eq,←T.card_eq_row]; exact hd)
      (by simpa only [ht] using hp)
    rcases hr with hb|⟨h8,horder⟩|h16|hsol
    · simpa only [M.degree_eq] using hb
    · exact (D.oneFactor_degreeEight_card_ne_1344 hk published8
        (M.degree_eq.symm.trans h8) (M.card_eq_row.trans horder)).elim
    · have hn : Nat.card X=16 := M.degree_eq.symm.trans h16
      have h := D.oneFactor_degreeSixteen_quotient_card_le_two hk published16 hn
      omega
    · have hsol' : TwoThirdsSolubleSimpleOrder (Nat.card D.Simple) := by
        rwa [T.card_eq_row]
      have hsolv := solvable_of_twoThirdsSolubleSimpleOrder D.Simple hsol'
      exact (D.noncommutative (isMulCommutative_iff.mpr
        (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv))).elim
  · have h := M.natural_quotient_card_le_two hm (finiteGroupSocle G)
      (D.oneFactor_socle_nontrivial hk)
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
