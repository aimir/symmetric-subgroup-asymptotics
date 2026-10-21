import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankFiveTopDerivedExhaustion
import SymmetricSubgroupAsymptotics.BinaryPairWideModuleSourceCardBounds
import SymmetricSubgroupAsymptotics.BinaryEightRegularTopCoverDirect

/-! The actual rank-five sixteen-point top has order at most1024 when
it supports the SAME original head-four outer kernel. Only actual inner
pair labels are conjugated, and no source splitting is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))
include F

theorem rank_five_top_card_le_1024_of_wide_original_kernel
    (hU : IsPGroup 2 U) (hTopRank : MarkedC4.genRank F.top.range = 5)
    (hwide : 4 ≤ MarkedC4.normalGen F.top.ker) : Nat.card F.top.range ≤ 1024 := by
  letI rankFiveTopOrderExhaustion_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI rankFiveTopOrderExhaustion_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  have hTop := F.top_isPGroup hU
  let W := F.axisNaturalSubrepresentation F.top.ker
  have hW : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants := by
    rw [← F.axisNatural_normalGen F.top.ker le_rfl hU]
    exact hwide
  obtain ⟨E⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  by_cases hregular : ∃ c : Equiv.Perm (Fin 8), MulAut.conj c • E.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)
  · obtain ⟨c, hc⟩ := hregular
    have hh : (E.reindex c).top.range = BinaryRegularEightNaturalRegistry.H := by
      rw [E.reindex_top_range_conjugation]
      exact hc
    exact (E.reindex c).source_card_le_1024_of_regular_top_wide_module hTop hh W hW
  by_cases hheisenberg : ∃ c : Equiv.Perm (Fin 8), MulAut.conj c • E.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)
  · obtain ⟨c, hc⟩ := hheisenberg
    have hh : (E.reindex c).top.range = BinaryHeisenbergEightNaturalHeads.H := by
      rw [E.reindex_top_range_conjugation]
      exact hc
    have hcard : Nat.card (E.reindex c).top.range = 32 := by rw [hh]; exact BinaryMenuCayley8T22.exact_card
    have hreg : BinaryRegularEightNaturalRegistry.H ≤ (E.reindex c).top.range := by
      rw [hh]
      exact BinaryHeisenbergEightNaturalHeads.regular_le
    exact (E.reindex c).source_card_le_1024_of_order_thirty_two_regular_subgroup_wide_module hTop
      ((E.reindex c).inner_top_not_elementary_of_card_thirty_two hTop hcard) hreg hcard W hW
  rcases E.rank_five_residual_high_top_dispatch hTop hTopRank.ge hregular hheisenberg with
    hsmall | ⟨c, h29 | h30 | h31⟩
  · letI rankFiveTopOrderExhaustion_innerTransitive : MulAction.IsPretransitive E.top.range (Fin 8) :=
      E.top_pretransitive
    have hnon : ¬ ∀ g : E.top.range, g ^ 2 = 1 := by
      intro hel
      exact hregular (BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
        E.top.range (E.top_isPGroup hTop) (fun i j => MulAction.exists_smul_eq E.top.range i j)
        (by intro t i; change (t ^ 2).val i = i; rw [hel]; rfl))
    by_cases hsmall16 : Nat.card E.top.range ≤ 16
    · exact E.source_card_le_1024_of_small_nonelementary_top_wide_module hTop hnon hsmall16 W hW
    have hcard32 : Nat.card E.top.range = 32 := by
      obtain ⟨k, hk⟩ := (E.top_isPGroup hTop).exists_card_eq
      have hk5 : k ≤ 5 := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
        (by rw [← hk]; exact hsmall)
      have hk4 : ¬ k ≤ 4 := by
        intro h
        apply hsmall16
        calc
          Nat.card E.top.range = 2 ^ k := hk
          _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h
          _ = 16 := by decide
      have he : k = 5 := by omega
      rw [hk, he]
      decide
    letI rankFiveTopOrderExhaustion_pairAction : MulAction F.top.range (Fin 8) :=
      MulAction.compHom (Fin 8) E.top
    have hact : ∀ (g : F.top.range) (i : Fin 8), g • i = E.top g i := fun _ _ => rfl
    obtain ⟨_, _, ht, _, _, _⟩ := E.rank_five_residual_top_saturation
      hact hTop hTopRank.ge hregular hheisenberg
    have hno := E.no_top_singlePowerOrbit_of_rank_five hact hTop hTopRank.ge ht.le
    obtain ⟨c, hc18 | hc19 | hc21 | hc22⟩ := BinaryEightOrderThirtyTwoResidualCover.cover
      E.top.range (E.top_isPGroup hTop) (fun i j => MulAction.exists_smul_eq E.top.range i j)
      hcard32 ht.ge hno
    · have hh : (E.reindex c).top.range = BinaryEightTop18AugmentationHead.H := by
        rw [E.reindex_top_range_conjugation]; exact hc18
      have hcard : Nat.card (E.reindex c).top.range = 32 := by rw [hh]; exact BinaryMenuCayley8T18.exact_card
      have hreg : BinaryRegularEightNaturalRegistry.H ≤ (E.reindex c).top.range := by
        rw [hh]
        exact BinaryEightRegularTopCoverDirect.regular_le_eighteen
      exact (E.reindex c).source_card_le_1024_of_order_thirty_two_regular_subgroup_wide_module hTop
        ((E.reindex c).inner_top_not_elementary_of_card_thirty_two hTop hcard) hreg hcard W hW
    · have hh : (E.reindex c).top.range = BinaryEightTop19AugmentationHead.H := by
        rw [E.reindex_top_range_conjugation]; exact hc19
      have hcard : Nat.card (E.reindex c).top.range = 32 := by rw [hh]; exact BinaryMenuCayley8T19.exact_card
      have hreg : BinaryRegularEightNaturalRegistry.H ≤ (E.reindex c).top.range := by
        rw [hh]
        exact BinaryEightRegularTopCoverDirect.regular_le_nineteen
      exact (E.reindex c).source_card_le_1024_of_order_thirty_two_regular_subgroup_wide_module hTop
        ((E.reindex c).inner_top_not_elementary_of_card_thirty_two hTop hcard) hreg hcard W hW
    · let e := actionConjugacyEquiv c hc21
      have hm := BinaryEightTopTwentyOneRankBound.genRank_le_two
      have hb := MarkedC4.ActualGlobalMarkGeneratorRank.genRank_le_of_surjective
        e.symm.toMonoidHom e.symm.surjective
      change MarkedC4.genRank E.top.range ≤
        MarkedC4.genRank BinaryEightTopTwentyOneRankBound.H at hb
      have hle : MarkedC4.genRank E.top.range ≤ 2 := hb.trans hm
      have ht3 : 3 ≤ MarkedC4.genRank E.top.range := ht.ge
      exact ((by decide : ¬ (3 ≤ (2 : ℕ))) (ht3.trans hle)).elim
    · exact (hheisenberg ⟨c, hc22⟩).elim
  · have hb := (E.reindex c).naturalModuleHead_le_three_of_top_twenty_nine_rank_five
      hTop hTopRank.ge h29 W
    omega
  · have hb := (E.reindex c).genRank_le_four_of_top_thirty hTop h30
    omega
  · have hJ := (E.reindex c).kernelSpace_eq_chart44_of_top_thirty_one_rank_five_head_four
      hTop hTopRank.ge h31 W hW
    have hd : Module.finrank (ZMod 2) (E.reindex c).kernelSpace ≤ 3 := by
      rw [hJ, BinaryRegularEightNaturalRegistry.chart44.finrank]
    have hc : Nat.card (E.reindex c).top.range = 64 := by rw [h31]; exact BinaryMenuCayley8T31.exact_card
    exact ((E.reindex c).source_card_le_of_kernel_dimension_and_top_card 3 64 hd hc.le).trans
      (by decide : 512 ≤ 1024)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
