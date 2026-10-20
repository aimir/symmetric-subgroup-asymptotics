import SymmetricSubgroupAsymptotics.BinaryPairLiteralModelStabilizers
import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightSaturatedExponent
import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisBounds
import SymmetricSubgroupAsymptotics.BinaryEightTopAbelianizationCards
import SymmetricSubgroupAsymptotics.BinaryDegreeEightLargeNormalIndex
import SymmetricSubgroupAsymptotics.NormalHeadActualIntersectionImage
import SymmetricSubgroupAsymptotics.PrimeIndexNormalAbelianizationLower
import SymmetricSubgroupAsymptotics.BinaryTransitiveAbelianizationQuarterPlusTwo
import SymmetricSubgroupAsymptotics.BinaryTransitiveProperNormalQuarterPlusOne
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank

/-! The sharp original proper-normal implication over the two literal
exceptional degree-eight tops. A proper rank-five original normal forces
its own index to be two. Full abelianization order saturation and the
actual lift carries then force six ordinary generators in the original
whole group. No degree-sixteen action catalogue is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8))

theorem regular_six_le_genRank_of_proper_normal_five
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤)
    (hN : 5 ≤ MarkedC4.normalGen N) : 6 ≤ MarkedC4.genRank U := by
  by_contra hbad
  have hgen : MarkedC4.genRank U ≤ 5 := by omega
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  have hk : f.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hTop : IsPGroup 2 F.top.range := F.top_isPGroup hU
  have hDproper : N.map f ≠ ⊤ := by
    intro hfull
    have hb := F.normalGen_add_one_le_top_of_full_actual_image hU N hfull hproper
    have ht := MarkedC4.ActualExcessOneQuotientRank.normalGen_top_le_genRank U
    omega
  have hTopCard : Nat.card F.top.range = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
  have hB : MarkedC4.normalGen (N ⊓ f.ker) ≤ 3 := by
    rw [hk]
    exact F.regular_axis_normalGen_le hU (N ⊓ F.top.ker) inf_le_right hH
  have hD : MarkedC4.normalGen (N.map f) ≤ 2 := by
    have hp := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card (N.map f)
    have hind : 2 ≤ (N.map f).index := (N.map f).one_lt_index_of_ne_top hDproper
    have hc := (N.map f).card_mul_index
    rw [hTopCard] at hc
    have hcard : Nat.card (N.map f) ≤ 4 := by nlinarith
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hp.trans hcard)
  obtain ⟨heq, hBexact, hDexact⟩ :=
    pGroup_actual_intersection_head_additivity_of_saturation
      2 f hf N hU 3 2 (by omega) hB hD
  have hDindex : (N.map f).index = 2 := by
    exact normal_index_two_of_card_eight_normalGen_two hTopCard (N.map f)
      hDproper hDexact.ge
  have hDlarge : 2 < Nat.card (N.map f) := by
    have hc := (N.map f).card_mul_index
    rw [hTopCard, hDindex] at hc
    omega
  have hker : F.top.ker ≤ N := by
    apply F.regular_kernel_le_normal_of_head_equality hU N hH
    · rw [← hk]
      omega
    · exact hDlarge
    · have htransport (K : Subgroup U) [K.Normal] (he : f.ker = K) :
          Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
            Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ K)) +
              Module.finrank (ZMod 2)
                (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ K) N)) := by
        subst K
        exact heq
      exact htransport F.top.ker hk
  have hNindex : N.index = 2 :=
    (F.normal_index_eq_actual_image_index N hker).trans hDindex
  have hdegree : Nat.card X = 16 := by simpa only [Nat.card_fin] using F.card_points
  have habUpper : Nat.card (Abelianization U) ≤ 64 := by
    have hb := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
    simpa only [hdegree] using hb
  have habLower : 64 ≤ Nat.card (Abelianization U) := by
    have hb := pGroup_normalGen_prime_index_le_abelianization_card 2 hU N hNindex
    have hp : 32 ≤ 2 ^ MarkedC4.normalGen N :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hN
    nlinarith
  have hab : Nat.card (Abelianization U) = 64 := by omega
  have hKexact : MarkedC4.normalGen F.top.ker = 3 := by
    rw [hk, inf_eq_right.mpr hker] at hBexact
    exact hBexact
  have htopAb : Nat.card (Abelianization F.top.range) = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).abelianizationCongr.toEquiv).trans
      BinaryEightTopAbelianizationCards.regular_abelianization_card
  have hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range) := by
    rw [hab, hKexact, htopAb]
    norm_num
  have hexp := F.regular_abelianization_pow_two_of_saturated_kernel hU hH
    (by omega) hsat
  have he := pGroup_abelianization_card_eq_pow_genRank 2 hU hexp
  have hp : 2 ^ MarkedC4.genRank U ≤ 32 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hgen
  omega

theorem heisenberg_six_le_genRank_of_proper_normal_five
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤)
    (hN : 5 ≤ MarkedC4.normalGen N) : 6 ≤ MarkedC4.genRank U := by
  by_contra hbad
  have hgen : MarkedC4.genRank U ≤ 5 := by omega
  let f := F.top.rangeRestrict
  have hf : Function.Surjective f := F.top.rangeRestrict_surjective
  have hk : f.ker = F.top.ker := MonoidHom.ker_rangeRestrict F.top
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hTop : IsPGroup 2 F.top.range := F.top_isPGroup hU
  have hDproper : N.map f ≠ ⊤ := by
    intro hfull
    have hb := F.normalGen_add_one_le_top_of_full_actual_image hU N hfull hproper
    have ht := MarkedC4.ActualExcessOneQuotientRank.normalGen_top_le_genRank U
    omega
  have hTopCard : Nat.card F.top.range = 32 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T22.exact_card
  have hB : MarkedC4.normalGen (N ⊓ f.ker) ≤ 2 := by
    rw [hk]
    exact F.heisenberg_axis_normalGen_le hU (N ⊓ F.top.ker) inf_le_right hH
  have hD : MarkedC4.normalGen (N.map f) ≤ 3 := by
    have hb := twoGroup_transitive_proper_normalGen_le_quarter_add_one
      F.top.range hTop (N.map f) hDproper
    simpa only [Nat.card_fin] using hb
  obtain ⟨heq, hBexact, hDexact⟩ :=
    pGroup_actual_intersection_head_additivity_of_saturation
      2 f hf N hU 2 3 (by omega) hB hD
  have hDindex : (N.map f).index = 2 := by
    exact transitive_degree_eight_card_thirty_two_normal_index_two
      (X := Fin 8) hTop (by simp only [Nat.card_fin]) hTopCard
      (N.map f) hDproper hDexact.ge
  have hDlarge : 8 < Nat.card (N.map f) := by
    have hc := (N.map f).card_mul_index
    rw [hTopCard, hDindex] at hc
    omega
  have hker : F.top.ker ≤ N := by
    apply F.heisenberg_kernel_le_normal_of_head_equality hU N hH
    · rw [← hk]
      omega
    · exact hDlarge
    · have htransport (K : Subgroup U) [K.Normal] (he : f.ker = K) :
          Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
            Module.finrank (ZMod 2) (primeRelativeCharacters 2 (N ⊓ K)) +
              Module.finrank (ZMod 2)
                (primeRelativeCharacters 2 (normalChainQuotient (N ⊓ K) N)) := by
        subst K
        exact heq
      exact htransport F.top.ker hk
  have hNindex : N.index = 2 :=
    (F.normal_index_eq_actual_image_index N hker).trans hDindex
  have hdegree : Nat.card X = 16 := by simpa only [Nat.card_fin] using F.card_points
  have habUpper : Nat.card (Abelianization U) ≤ 64 := by
    have hb := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
    simpa only [hdegree] using hb
  have habLower : 64 ≤ Nat.card (Abelianization U) := by
    have hb := pGroup_normalGen_prime_index_le_abelianization_card 2 hU N hNindex
    have hp : 32 ≤ 2 ^ MarkedC4.normalGen N :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hN
    nlinarith
  have hab : Nat.card (Abelianization U) = 64 := by omega
  have hKexact : MarkedC4.normalGen F.top.ker = 2 := by
    rw [hk, inf_eq_right.mpr hker] at hBexact
    exact hBexact
  have htopAb : Nat.card (Abelianization F.top.range) = 16 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).abelianizationCongr.toEquiv).trans
      BinaryEightTopAbelianizationCards.heisenberg_abelianization_card
  have hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range) := by
    rw [hab, hKexact, htopAb]
    norm_num
  have hexp := F.heisenberg_abelianization_pow_two_of_saturated_kernel hU hH
    (by omega) hsat
  have he := pGroup_abelianization_card_eq_pow_genRank 2 hU hexp
  have hp : 2 ^ MarkedC4.genRank U ≤ 32 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hgen
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
