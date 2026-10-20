import SymmetricSubgroupAsymptotics.PrimitiveSocleTwoActionHeadReduction
import SymmetricSubgroupAsymptotics.PrimitiveCompositionAffineHeadReduction
import SymmetricSubgroupAsymptotics.PrimitiveSmallExceptionalSocleFactors
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadPublished

/-! The strict-head and primitive-degree18 consumers from the single retained
actual-order composition correspondence and the already retained XL ordinary
simple-index bound. No253-row or116-row correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

private theorem natural_match_head_zero
    {G X : Type} [Group G] [Finite G] [Finite X]
    (M : PrimitiveCompositionCatalogueMatch G X)
    (hn : (primitiveCompositionBoundRow M.row).kind≠.orderBound)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)=0 := by
  have hf : 5≤Nat.card X := by
    have h := (primitiveCompositionBoundRow M.row).natural_degree hn
    rwa [M.degree_eq] at h
  cases hk : (primitiveCompositionBoundRow M.row).kind with
  | orderBound => exact (hn hk).elim
  | naturalAlternating =>
      obtain ⟨e⟩ := M.alternating_equiv hk
      exact primeRelativeHead_eq_zero_of_actualChiefWeight_zero N (actualChiefSeries G)
        (allChiefSeries_zero_of_alternating_equiv (Nat.card X) hf e (actualChiefSeries G))
  | naturalSymmetric =>
      obtain ⟨e⟩ := M.symmetric_equiv hk
      exact primeRelativeHead_eq_zero_of_actualChiefWeight_zero N (actualChiefSeries G)
        (allChiefSeries_zero_of_symmetric_equiv (Nat.card X) hf e (actualChiefSeries G))

private theorem primitive_degreeSix_strictHead_from_composition
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hX : Nat.card X=6) (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  obtain ⟨M⟩ := catalogue G X (by omega)
  by_cases hm : (primitiveCompositionBoundRow M.row).kind=.orderBound
  · obtain ⟨D⟩ := publishedONanScottStructure G X
    cases D with
    | inl D =>
        have hk := D.factorCount_eq_one_of_small_head_degree (Or.inl hX)
        exact D.oneFactor_ternaryHead_strict_from_composition hk catalogue hindex M hm
          (by dsimp only [PrimitiveSmallSocleHeadDegree]; omega) (by omega) N
    | inr P =>
        have hp := P.degree_isPrimePow inferInstance
        rw [hX] at hp
        exact ((show ¬ IsPrimePow (6 : ℕ) by decide) hp).elim
  · rw [natural_match_head_zero M hm N]
    omega

/-- The exact strict normal-head consumer uses the one actual-order
composition correspondence at both the original action and the actual simple
least-index action. The infinite-tail input remains unchanged. -/
theorem primitiveTernaryStrictHeadBound_of_composition_and_simpleIndex
    (hgen : PrimitiveNormalGeneratorInput)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds) : PrimitiveTernaryStrictHeadBound := by
  intro G X _ _ _ _ _ _ _ h3 h4 h18 N _
  by_cases hlarge : 34≤Nat.card X
  · exact c1_primitive_relative_tail_faithful hgen hlarge N
  by_cases h6 : Nat.card X=6
  · exact primitive_degreeSix_strictHead_from_composition catalogue hindex G X h6 N
  obtain ⟨M⟩ := catalogue G X (by omega)
  rcases M.strictHead_or_exceptional (by omega) h3 h4 h6 h18 N with hex|hb
  · by_cases hm : (primitiveCompositionBoundRow M.row).kind=.orderBound
    · obtain ⟨D⟩ := publishedONanScottStructure G X
      cases D with
      | inl D =>
          have hd : Nat.card X=6 ∨ Nat.card X=9 ∨ Nat.card X=10 ∨ Nat.card X=11 ∨
              Nat.card X=12 ∨ Nat.card X=13 ∨ Nat.card X=18 ∨ Nat.card X=27 := by
            dsimp only [PrimitiveStrictHeadExceptionalDegree] at hex
            omega
          have hk := D.factorCount_eq_one_of_small_head_degree hd
          by_cases h27 : Nat.card X=27
          · exact D.oneFactor_ternaryHead_strict_of_degree_ge_fourteen hk hindex
              (by omega) (by omega) N
          · have hs : PrimitiveSmallSocleHeadDegree (Nat.card X) := by
              dsimp only [PrimitiveSmallSocleHeadDegree]
              dsimp only [PrimitiveStrictHeadExceptionalDegree] at hex
              omega
            exact D.oneFactor_ternaryHead_strict_from_composition hk catalogue hindex M hm hs h18 N
      | inr P => exact M.affine_strictHead_of_exceptional P hex N
    · rw [natural_match_head_zero M hm N]
      have hn : 0<Nat.card X := Nat.card_pos
      omega
  · exact hb

/-- The actual primitive degree18 head vanishes by the same two-action
order comparison, without the old strict or simple-socle catalogues. -/
theorem primitive_degreeEighteen_ternaryHead_eq_zero_from_composition
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (hX : Nat.card X=18) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)=0 := by
  obtain ⟨M⟩ := catalogue G X (by omega)
  by_cases hm : (primitiveCompositionBoundRow M.row).kind=.orderBound
  · obtain ⟨D⟩ := publishedONanScottStructure G X
    cases D with
    | inl D =>
        have hd : Nat.card X=6 ∨ Nat.card X=9 ∨ Nat.card X=10 ∨ Nat.card X=11 ∨
            Nat.card X=12 ∨ Nat.card X=13 ∨ Nat.card X=18 ∨ Nat.card X=27 := by omega
        exact D.oneFactor_degreeEighteen_head_eq_zero_from_composition
          (D.factorCount_eq_one_of_small_head_degree hd) catalogue hindex M hm hX N
    | inr P =>
        have hp := P.degree_isPrimePow inferInstance
        rw [hX] at hp
        exact ((show ¬ IsPrimePow (18 : ℕ) by decide) hp).elim
  · exact natural_match_head_zero M hm N

end SymmetricSubgroupAsymptotics
