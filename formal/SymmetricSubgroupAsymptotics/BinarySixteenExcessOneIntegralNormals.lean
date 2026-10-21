import SymmetricSubgroupAsymptotics.BinaryPairRegularExcessOneIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergExcessOneIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairSixtyFourTopExcessOneIntegralNormals
import SymmetricSubgroupAsymptotics.BinaryPairRankFiveHighTopDispatch

/-! Complete INTEGRAL proper-normal bound in the actual transitive binary
sixteen-point excess-one source. Pair reindexing retains the original group
and every original normal; no mod-two head substitutes for quotient order. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure

/-- Every proper original normal satisfies the full integral order bound. -/
theorem binary_sixteen_excess_one_proper_normal_integral_order_le_sixteen
    (G : Subgroup (Equiv.Perm (Fin 16))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 16, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 16 1) (E : Subgroup G) [E.Normal] (hproper : E ≠ ⊤) :
    normalIntegralCoinvariantOrder E ≤ 16 := by
  letI sixteenIntegralProof_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI sixteenIntegralProof_originalTransitive : MulAction.IsPretransitive G (Fin 16) := ⟨htrans⟩
  have hrank := degree_sixteen_excess_one_genRank_eq_five G hG htrans hexcess
  have hhigh : 5 ≤ genRank G := by omega
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 3 G hG (by norm_num only [Nat.card_fin])
  by_cases hregular : ∃ c : Equiv.Perm (Fin 8), MulAut.conj c • F.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)
  · obtain ⟨c, hc⟩ := hregular
    have hh : (F.reindex c).top.range = BinaryRegularEightNaturalRegistry.H := by
      rw [F.reindex_top_range_conjugation]
      exact hc
    have hp := (F.reindex c).top_isPGroup hG
    letI sixteenIntegralProof_regularNilpotent : Group.IsNilpotent (F.reindex c).top.range := hp.isNilpotent
    have hcard : Nat.card (F.reindex c).top.range = 8 := by
      rw [hh]
      exact BinaryMenuCayley8T3.exact_card
    have htoprank : genRank (F.reindex c).top.range ≤ 3 := by
      have hb := ActualNormalGeneratorDensity.two_pow_normalGen_le_card
        (⊤ : Subgroup (F.reindex c).top.range)
      rw [Subgroup.card_top, hcard] at hb
      have hn : normalGen (⊤ : Subgroup (F.reindex c).top.range) ≤ 3 :=
        (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
      exact (genRank_le_normalGen_top (G := (F.reindex c).top.range)).trans hn
    exact (F.reindex c).regular_pair_top_excess_one_proper_normal_integral_order_le_sixteen
      hG htrans hexcess hh htoprank E hproper
  by_cases hheisenberg : ∃ c : Equiv.Perm (Fin 8), MulAut.conj c • F.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)
  · obtain ⟨c, hc⟩ := hheisenberg
    have hh : (F.reindex c).top.range = BinaryHeisenbergEightNaturalHeads.H := by
      rw [F.reindex_top_range_conjugation]
      exact hc
    exact (F.reindex c).heisenberg_pair_top_excess_one_proper_normal_integral_order_le_sixteen
      hG htrans hexcess hh E hproper
  letI sixteenIntegralProof_topTransitive : MulAction.IsPretransitive F.top.range (Fin 8) :=
    F.top_pretransitive
  letI sixteenIntegralProof_pairAction : MulAction G (Fin 8) := MulAction.compHom (Fin 8) F.top
  letI sixteenIntegralProof_pairTransitive : MulAction.IsPretransitive G (Fin 8) := ⟨by
    intro i j
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨g, rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨g, ht⟩⟩
  have hact : ∀ (g : G) (i : Fin 8), g • i = F.top g i := fun _ _ => rfl
  obtain ⟨_, _, htoprank, _, _, _⟩ :=
    F.rank_five_residual_top_saturation hact hG hhigh hregular hheisenberg
  have hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := G) (X := Fin 8) := by
    intro hel
    apply hregular
    apply BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
      F.top.range (F.top_isPGroup hG)
      (fun i j => MulAction.exists_smul_eq F.top.range i j)
    intro t i
    obtain ⟨g, rfl⟩ := F.top.rangeRestrict_surjective t
    rw [← map_pow]
    exact (hact (g ^ 2) i).symm.trans (hel g i)
  have hcard : Nat.card F.top.range ≤ 64 := by
    rcases F.rank_five_residual_high_top_dispatch hG hhigh hregular hheisenberg with
      hsmall | ⟨c, h29 | h30 | h31⟩
    · exact hsmall.trans (by decide : 32 ≤ 64)
    · have hc := Nat.card_congr (actionConjugacyEquiv c
        ((F.reindex_top_range_conjugation c).symm.trans h29)).toEquiv
      rw [BinaryMenuCayley8T29.exact_card] at hc
      exact hc.le
    · have hc := Nat.card_congr (actionConjugacyEquiv c
        ((F.reindex_top_range_conjugation c).symm.trans h30)).toEquiv
      rw [BinaryMenuCayley8T30.exact_card] at hc
      exact hc.le
    · have hc := Nat.card_congr (actionConjugacyEquiv c
        ((F.reindex_top_range_conjugation c).symm.trans h31)).toEquiv
      rw [BinaryMenuCayley8T31.exact_card] at hc
      exact hc.le
  exact F.sixtyfour_pair_top_excess_one_proper_normal_integral_order_le_sixteen
    hact hG htrans hexcess hnon hcard htoprank.le E hproper

end SymmetricSubgroupAsymptotics
