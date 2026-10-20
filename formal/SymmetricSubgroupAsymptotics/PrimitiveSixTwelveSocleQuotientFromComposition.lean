import SymmetricSubgroupAsymptotics.PrimitiveCompositionSixTwelveQuotientReceipt
import SymmetricSubgroupAsymptotics.SimpleOrder1320TwelvePointExclusion
import SymmetricSubgroupAsymptotics.PrimitiveNaturalSocleQuotient
import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart
import SymmetricSubgroupAsymptotics.SimpleSocleQuotientOrderBudget
import SymmetricSubgroupAsymptotics.PrimitiveSmallExceptionalSocleFactors

/-! The exact degree6/12 normal-lattice consumer uses the same actual
composition correspondence and original simple-index bound. The single
residual arithmetic pair is excluded by its actual twelve-point action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

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

theorem NonaffineData.oneFactor_sixTwelve_quotient_orderBound
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds)
    (M : PrimitiveCompositionCatalogueMatch G X)
    (hkind : (primitiveCompositionBoundRow M.row).kind=.orderBound)
    (hn : Nat.card X=6 ∨ Nat.card X=12) :
    Nat.card (G⧸finiteGroupSocle G)≤2 := by
  have hsmall : Nat.card X≤18 := by omega
  obtain ⟨ell,hell,hfive,helln,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  have hq : Nat.card (G⧸finiteGroupSocle G)<15 :=
    quotient_order_lt_fifteen_of_log (by omega) (by omega) hlog
  obtain ⟨H,hH,hi,⟨T⟩⟩ := compositionMatch_at_leastIndex
    catalogue D.noncommutative hell (by omega)
  have ht : (primitiveCompositionBoundRow T.row).degree=ell :=
    T.degree_eq.trans (H.index_eq_card.symm.trans hi)
  have hsocle : Nat.card (finiteGroupSocle G)=Nat.card D.Simple :=
    Nat.card_congr (D.oneFactorEquiv hk).toEquiv
  have hfactor : Nat.card (G⧸finiteGroupSocle G)*Nat.card D.Simple=Nat.card G := by
    rw [←hsocle]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)).symm
  letI : MulAction.IsPretransitive (finiteGroupSocle G) X := D.socle_transitive
  have hdiv : Nat.card X∣Nat.card D.Simple := by
    rw [←hsocle]
    exact degree_dvd_card_of_transitive_normal (X := X) (finiteGroupSocle G)
  have hp := two_pow_le_cube_of_log (by omega) hlog
  have hr := primitiveComposition_twoAction_sixTwelve_receipt M.row T.row
    (Nat.card (G⧸finiteGroupSocle G)) Nat.card_pos hq hkind
    (by simpa only [M.degree_eq] using hn)
    (by rwa [ht]) (by rwa [ht,M.degree_eq])
    (by rw [←T.card_eq_row,←M.card_eq_row]; exact hfactor)
    (by rw [M.degree_eq,←T.card_eq_row]; exact hdiv)
    (by simpa only [ht] using hp)
  rcases hr with hb|⟨h12,h1320⟩
  · exact hb
  · letI : FaithfulSMul D.Simple (D.Simple⧸H) :=
      ⟨fun {_ _} h => simple_cosetAction_injective H hH (Equiv.ext h)⟩
    exact (no_nonabelian_simple_order1320_twelvePoint_action D.noncommutative
      (T.card_eq_row.trans h1320) (T.degree_eq.symm.trans h12)).elim

theorem NonaffineData.sixTwelve_socle_quotient_card_le_two
    (D : NonaffineData G X)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds)
    (hn : Nat.card X=6 ∨ Nat.card X=12) :
    Nat.card (G⧸finiteGroupSocle G)≤2 := by
  have hk := D.factorCount_eq_one_of_small_head_degree (by omega)
  obtain ⟨M⟩ := catalogue G X (by omega)
  by_cases hm : (primitiveCompositionBoundRow M.row).kind=.orderBound
  · exact D.oneFactor_sixTwelve_quotient_orderBound hk catalogue hindex M hm hn
  · exact M.natural_quotient_card_le_two hm (finiteGroupSocle G)
      (D.oneFactor_socle_nontrivial hk)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

namespace SymmetricSubgroupAsymptotics

theorem primitive_degreeSix_five_dvd_from_composition
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hX : Nat.card X=6) : 5∣Nat.card G := by
  obtain ⟨M⟩ := catalogue G X (by omega)
  rw [M.card_eq_row]
  exact primitiveComposition_degreeSix_five_dvd M.row (M.degree_eq.trans hX)

end SymmetricSubgroupAsymptotics
