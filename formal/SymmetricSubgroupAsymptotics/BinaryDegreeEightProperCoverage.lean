import SymmetricSubgroupAsymptotics.TransitiveNormalRankCardGap
import SymmetricSubgroupAsymptotics.BinaryDegreeEightProperHeadProfiles
import SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalProof
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T15
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T16
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T17
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T18
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T19
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T20
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T21
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T28
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T29
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T30
import SymmetricSubgroupAsymptotics.RDTDegreeEightProperNormalWords8T31

/-! Complete sharp degree-eight proper-normal coverage from the already
checked original action registry, generic low-order rank gap, existing
original head profiles, and separately checked selected sparse words.
The exceptional alternative is an actual group equivalence to the same
faithful eight-point Heisenberg action. No catalogue input is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightProperCoverage

open RDTDegreeEightExceptionalTransport BinaryActionRegistry8

/-- Ambient normal rank and properness transport through the SAME actual
group equivalence. -/
theorem proper_normal_bounds_of_equiv
    {G H : Type} [Group G] [Finite G] [Group H] [Finite H] (e : G ≃* H)
    (hbound : ∀ (N : Subgroup G) [N.Normal], N ≠ ⊤ → MarkedC4.normalGen N ≤ 2) :
    ∀ (N : Subgroup H) [N.Normal], N ≠ ⊤ → MarkedC4.normalGen N ≤ 2 := by
  intro N _ hproper
  let M := N.map e.symm.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  have hMproper : M ≠ ⊤ := by
    intro htop
    apply hproper
    apply top_unique
    intro n _
    have hn : e.symm n ∈ M := by rw [htop]; trivial
    obtain ⟨m, hm, he⟩ := hn
    exact (e.symm.injective he) ▸ hm
  have hb := hbound M hMproper
  rwa [normalGen_map_equiv e.symm N] at hb

/-- Every original eight-point binary group either has only small proper
normal ranks or is the actual exceptional Heisenberg group. -/
theorem proper_normal_bounds_or_heisenberg
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8, ∃ g : G, g.val x = y) :
    (∀ (N : Subgroup G) [N.Normal], N ≠ ⊤ → MarkedC4.normalGen N ≤ 2) ∨
      Nonempty (G ≃* BinaryHeisenberg 2) := by
  letI : MulAction.IsPretransitive G (Fin 8) := ⟨htrans⟩
  have ht : PermutationSubgroupTransitive G := by
    intro x y
    obtain ⟨g, hg⟩ := htrans x y
    exact ⟨g.val, g.property, hg⟩
  obtain ⟨i, g, hg⟩ := BinaryActionRegistry8.complete G hG ht
  let e := actionConjugacyEquiv g hg
  fin_cases i
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T1.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T1.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T2.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T2.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T3.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T4.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T4.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T5.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T5.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T6.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T6.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T7.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T7.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T8.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T8.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T9.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T9.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T10.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T10.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    have hcard : Nat.card G ≤ 16 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T11.generators)) ≤ 16
      norm_num only [BinaryMenuCayley8T11.exact_card]
    intro N _ hproper
    exact twoGroup_transitive_degree_eight_small_order_proper_normalGen_le_two
      (X := Fin 8) hG (by simp only [Nat.card_fin]) hcard N hproper
  · left
    letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T15.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T15.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T15.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T16.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T16.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T16.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T17.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T17.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T17.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T18.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T18.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T18.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T19.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T19.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T19.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T20.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T20.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T20.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T21.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T21.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T21.all_normal_bound
  · right
    exact ⟨e.trans RDTDegreeEightE8Action.modelEquiv.symm⟩
  · left
    letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T26.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T26.originalEquiv.trans e.symm)
      BinaryDegreeEightProperHeadProfiles.proper_normal_bound_8T26
  · left
    letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T27.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T27.originalEquiv.trans e.symm)
      BinaryDegreeEightProperHeadProfiles.proper_normal_bound_8T27
  · left
    letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T28.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T28.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T28.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T29.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T29.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T29.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T30.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T30.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T30.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T31.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T31.originalEquiv.trans e.symm)
      RDTDegreeEightProperNormalWords8T31.all_normal_bound
  · left
    letI : Group (FiniteGroupRow 128) := BinaryMenuCayley8T35.group
    exact proper_normal_bounds_of_equiv (BinaryMenuCayley8T35.originalEquiv.trans e.symm)
      BinaryDegreeEightProperHeadProfiles.proper_normal_bound_8T35

end SymmetricSubgroupAsymptotics.BinaryDegreeEightProperCoverage
