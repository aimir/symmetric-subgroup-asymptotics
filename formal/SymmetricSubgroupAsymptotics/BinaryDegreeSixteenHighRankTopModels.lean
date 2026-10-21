import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenExcessProfile
import SymmetricSubgroupAsymptotics.AbelianKernelOrdinaryGeneration

/-! A six-generator original degree-sixteen action retains one of two
literal eight-point top actions and a large actual pair-kernel head.
This does not classify six-generator degree-sixteen actions themselves. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightHighRankAction

open MarkedC4 MarkedC4.RDTExcessStructure RDTDegreeEightExceptionalTransport

/-- High ordinary rank recognizes the same original Heisenberg action. -/
theorem four_le_genRank_action_conjugate_heisenberg
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8, ∃ g : G, g.val x = y)
    (hfour : 4 ≤ genRank G) :
    ∃ g : Equiv.Perm (Fin 8), MulAut.conj g • G =
      Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) := by
  letI : MulAction.IsPretransitive G (Fin 8) := ⟨htrans⟩
  letI : Group.IsNilpotent G := hG.isNilpotent
  have hall (N : Subgroup G) [N.Normal] : normalGen N ≤ 4 := by
    simpa only [Nat.card_fin] using twoGroup_transitive_normalGen_le_quarter_add_two G hG N
  have heq : normalGen (⊤ : Subgroup G) = 4 := by
    have hlo := hfour.trans (genRank_le_normalGen_top (G := G))
    have hhi := hall (⊤ : Subgroup G)
    omega
  have hexcess : HasExcess G 8 2 := by
    constructor
    · exact ⟨⊤, inferInstance, by norm_num [heq]⟩
    · intro N hN
      letI := hN
      have hb := hall N
      norm_num
      exact hb
  have ht : PermutationSubgroupTransitive G := by
    intro x y
    obtain ⟨g, hg⟩ := htrans x y
    exact ⟨g.val, g.property, hg⟩
  obtain ⟨i, g, hg⟩ := BinaryActionRegistry8.complete G hG ht
  have hi : i = 18 := RDTDegreeEightExceptionalProof.index_eq_e8 i
    (hasExcess_of_equiv (actionConjugacyEquiv g hg) hexcess)
  subst i
  exact ⟨g, hg⟩

end SymmetricSubgroupAsymptotics.BinaryDegreeEightHighRankAction

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8))

/-- Ordinary generation uses only the actual elementary kernel and the
actual top range; arbitrary lift offsets are allowed. -/
theorem genRank_le_actual_pair_kernel_add_top :
    MarkedC4.genRank U ≤ MarkedC4.normalGen F.top.ker + MarkedC4.genRank F.top.range := by
  letI : IsMulCommutative F.top.ker := ⟨⟨fun a b => F.bitsHom_injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  letI : IsMulCommutative F.top.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  have hb := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    F.top.rangeRestrict F.top.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hb
  omega

private theorem actual_top_genRank_le_four
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U) :
    MarkedC4.genRank F.top.range ≤ 4 := by
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hp := F.top_isPGroup hU
  letI : Group.IsNilpotent F.top.range := hp.isNilpotent
  have hb := twoGroup_transitive_normalGen_le_quarter_add_two F.top.range hp
    (⊤ : Subgroup F.top.range)
  norm_num only [Nat.card_fin] at hb
  exact (MarkedC4.genRank_le_normalGen_top (G := F.top.range)).trans hb

/-- The only two top templates needed for the joint width/rank frontier.
The original group is unchanged by reindexing physical pair labels. -/
theorem six_le_genRank_literal_top_models
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 6 ≤ MarkedC4.genRank U) :
    (∃ g : Equiv.Perm (Fin 8),
      (F.reindex g).top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ∧
      3 ≤ MarkedC4.normalGen (F.reindex g).top.ker) ∨
    (∃ g : Equiv.Perm (Fin 8),
      (F.reindex g).top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) ∧
      2 ≤ MarkedC4.normalGen (F.reindex g).top.ker) := by
  letI : MulAction.IsPretransitive F.top.range (Fin 8) := F.top_pretransitive
  have hTop := F.top_isPGroup hU
  have htrans : ∀ i j : Fin 8, ∃ t : F.top.range, t.val i = j := by
    intro i j
    exact MulAction.exists_smul_eq F.top.range i j
  letI : MulAction U (Fin 8) := {
    smul := fun u i => F.top u i
    one_smul := by intro i; change F.top 1 i = i; rw [map_one]; rfl
    mul_smul := by
      intro u v i
      change F.top (u * v) i = F.top u (F.top v i)
      rw [map_mul]
      rfl }
  have hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i := fun _ _ => rfl
  letI : MulAction.IsPretransitive U (Fin 8) := ⟨fun i j => by
    obtain ⟨t, ht⟩ := htrans i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u, ht⟩⟩
  by_cases hel : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 8)
  · have htopel : BinarySquareActionStructure.SquaresActTrivially
        (G := F.top.range) (X := Fin 8) := by
      intro t i
      obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
      rw [← map_pow]
      exact hel u i
    obtain ⟨g, hg⟩ := BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
      F.top.range hTop htrans htopel
    have hH : (F.reindex g).top.range =
        Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) :=
      (F.reindex_top_range_conjugation g).trans hg
    have hp := (F.reindex g).top_isPGroup hU
    letI : Group.IsNilpotent (F.reindex g).top.range := hp.isNilpotent
    have hcard : Nat.card (F.reindex g).top.range = 8 :=
      (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans BinaryMenuCayley8T3.exact_card
    have ht : MarkedC4.genRank (F.reindex g).top.range ≤ 3 := by
      have hb := MarkedC4.ActualNormalGeneratorDensity.two_pow_normalGen_le_card
        (⊤ : Subgroup (F.reindex g).top.range)
      rw [Subgroup.card_top, hcard] at hb
      have hn : MarkedC4.normalGen (⊤ : Subgroup (F.reindex g).top.range) ≤ 3 :=
        (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
      exact (MarkedC4.genRank_le_normalGen_top (G := (F.reindex g).top.range)).trans hn
    have hb := (F.reindex g).genRank_le_actual_pair_kernel_add_top
    exact Or.inl ⟨g, hH, by omega⟩
  · have hk := F.normalGen_le_quarter_of_not_elementary hact hU hel F.top.ker le_rfl
    norm_num only [Nat.card_fin] at hk
    have hb := F.genRank_le_actual_pair_kernel_add_top
    have hfour : 4 ≤ MarkedC4.genRank F.top.range := by omega
    obtain ⟨g, hg⟩ := BinaryDegreeEightHighRankAction.four_le_genRank_action_conjugate_heisenberg
      F.top.range hTop htrans hfour
    have hH : (F.reindex g).top.range =
        Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) :=
      (F.reindex_top_range_conjugation g).trans hg
    have ht := (F.reindex g).actual_top_genRank_le_four hU
    have hb' := (F.reindex g).genRank_le_actual_pair_kernel_add_top
    exact Or.inr ⟨g, hH, by omega⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
