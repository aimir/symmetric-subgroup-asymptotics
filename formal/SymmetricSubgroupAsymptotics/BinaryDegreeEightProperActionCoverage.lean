import SymmetricSubgroupAsymptotics.BinaryDegreeEightProperCoverage

/-! The proper-normal exception retains literal original-point conjugacy,
so its natural-module certificates apply to the same degree-eight action.
The complete checked26-row action coverage and all25 ordinary bounds are
the existing ones; no abstract-group-only replacement is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightProperActionCoverage

open RDTDegreeEightExceptionalTransport BinaryActionRegistry8
open BinaryDegreeEightProperCoverage

theorem proper_normal_bounds_or_heisenberg_action
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8, ∃ g : G, g.val x = y) :
    (∀ (N : Subgroup G) [N.Normal], N ≠ ⊤ → MarkedC4.normalGen N ≤ 2) ∨
      (∃ g : Equiv.Perm (Fin 8), MulAut.conj g • G =
        Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)) := by
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
    exact ⟨g, hg⟩
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


end SymmetricSubgroupAsymptotics.BinaryDegreeEightProperActionCoverage
