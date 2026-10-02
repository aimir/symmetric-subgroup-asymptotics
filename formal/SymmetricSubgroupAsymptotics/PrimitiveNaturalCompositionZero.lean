import SymmetricSubgroupAsymptotics.FiniteCompositionWitness
import SymmetricSubgroupAsymptotics.ChiefSeriesTransport
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.FinCases

/-!
# Uniform zero ternary weight for natural alternating and symmetric groups

The bounded primitive receipt has one systematic family on which the crude
order valuation is too large: the natural alternating and symmetric actions.
This file treats those rows symbolically.  The actual composition chains are
`1 < A_n` and `1 < A_n < S_n`; hence no composition factor has order three.
The conclusion applies to every chosen actual chief series.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The one-edge composition witness of a nontrivial simple group. -/
def simpleFiniteCompositionWitness (G : Type) [Group G] [IsSimpleGroup G] :
    FiniteCompositionWitness G where
  length := 1
  subgroup := ![⊥, ⊤]
  head := rfl
  last := rfl
  step i := by
    fin_cases i
    change NormalCompositionCover (⊥ : Subgroup G) ⊤
    letI : IsSimpleGroup (⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
    refine ⟨bot_lt_top, inferInstance, ?_⟩
    intro M hM _
    simpa only [Subgroup.bot_subgroupOf] using hM.eq_bot_or_eq_top

/-- Every chief series of a simple group whose order is not three has zero
ternary weight.  This is stronger than merely constructing one zero-weight
chief series. -/
theorem actualChiefSeriesTernaryWeight_eq_zero_of_simple
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G ≠ 3) (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c = 0 := by
  have hle := (simpleFiniteCompositionWitness G).chiefWeight_le c
  have hz : (simpleFiniteCompositionWitness G).orderCount 3 = 0 := by
    change (∑ i : Fin 1,
      if (![ ⊥, (⊤ : Subgroup G)] i.castSucc).relIndex
        (![ ⊥, (⊤ : Subgroup G)] i.succ) = 3 then 1 else 0) = 0
    rw [Fin.sum_univ_one]
    simp [hcard]
  omega

/-- The two-edge composition witness of an index-two extension of a simple
normal subgroup. -/
def indexTwoSimpleFiniteCompositionWitness
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hindex : N.index = 2) : FiniteCompositionWitness G where
  length := 2
  subgroup := ![⊥, N, ⊤]
  head := rfl
  last := rfl
  step i := by
    fin_cases i
    · change NormalCompositionCover (⊥ : Subgroup G) N
      refine ⟨(Subgroup.isSimpleGroup_iff.mp
        (inferInstance : IsSimpleGroup N)).1.bot_lt, inferInstance, ?_⟩
      intro M hM _
      simpa only [Subgroup.bot_subgroupOf] using hM.eq_bot_or_eq_top
    · change NormalCompositionCover N ⊤
      have hlt : N < ⊤ := lt_top_iff_ne_top.mpr (fun h => by
        rw [h, Subgroup.index_top] at hindex
        omega)
      letI : Fact ((N.subgroupOf (⊤ : Subgroup G)).index.Prime) := ⟨by
        have hi : (N.subgroupOf (⊤ : Subgroup G)).index = 2 := by
          change N.relIndex ⊤ = 2
          rwa [Subgroup.relIndex_top_right]
        rw [hi]
        exact Nat.prime_two⟩
      letI : IsSimpleGroup
          ((⊤ : Subgroup G) ⧸ N.subgroupOf (⊤ : Subgroup G)) :=
        isSimpleGroup_of_prime_card
          (p := (N.subgroupOf (⊤ : Subgroup G)).index) (by
            simpa only using
              (Subgroup.index_eq_card
                (H := N.subgroupOf (⊤ : Subgroup G))).symm)
      exact NormalCompositionCover.of_simple hlt

/-- Every chief series of an index-two extension of a simple group of
non-three order has zero ternary weight. -/
theorem actualChiefSeriesTernaryWeight_eq_zero_of_indexTwoSimple
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hindex : N.index = 2) (hcard : Nat.card N ≠ 3)
    (c : ActualChiefSeries G) : actualChiefSeriesTernaryWeight c = 0 := by
  let W := indexTwoSimpleFiniteCompositionWitness N hindex
  have hle := W.chiefWeight_le c
  have hz : W.orderCount 3 = 0 := by
    change (∑ i : Fin 2,
      if (![⊥, N, (⊤ : Subgroup G)] i.castSucc).relIndex
        (![⊥, N, (⊤ : Subgroup G)] i.succ) = 3 then 1 else 0) = 0
    rw [Fin.sum_univ_two]
    simp [Subgroup.relIndex_bot_left, Subgroup.relIndex_top_right, hindex, hcard]
  omega

private theorem alternating_card_ne_three (n : ℕ) (hn : 5 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) ≠ 3 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup]
  simp only [Nat.card_fin]
  have hfac : 120 ≤ n.factorial := by
    simpa using Nat.factorial_le hn
  have hmul : 60 * 2 ≤ n.factorial := by
    simpa using hfac
  have h60 : 60 ≤ n.factorial / 2 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 hmul
  omega

/-- Every chosen chief series of the natural alternating group in degree at
least five has zero ternary weight. -/
theorem naturalAlternating_allChiefSeries_zero (n : ℕ) (hn : 5 ≤ n)
    (c : ActualChiefSeries (alternatingGroup (Fin n))) :
    actualChiefSeriesTernaryWeight c = 0 := by
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  exact actualChiefSeriesTernaryWeight_eq_zero_of_simple _
    (alternating_card_ne_three n hn) c

/-- Every chosen chief series of the natural symmetric group in degree at
least five has zero ternary weight. -/
theorem naturalSymmetric_allChiefSeries_zero (n : ℕ) (hn : 5 ≤ n)
    (c : ActualChiefSeries (Equiv.Perm (Fin n))) :
    actualChiefSeriesTernaryWeight c = 0 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  exact actualChiefSeriesTernaryWeight_eq_zero_of_indexTwoSimple
    (alternatingGroup (Fin n)) alternatingGroup.index_eq_two
    (alternating_card_ne_three n hn) c

/-- Transport the uniform alternating conclusion through an arbitrary group
equivalence. -/
theorem allChiefSeries_zero_of_alternating_equiv
    {G : Type} [Group G] [Finite G] (n : ℕ) (hn : 5 ≤ n)
    (e : G ≃* alternatingGroup (Fin n)) (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c = 0 := by
  have h := naturalAlternating_allChiefSeries_zero n hn
    (actualChiefSeriesComap e.symm c)
  rwa [actualChiefSeriesComap_weight] at h

/-- Transport the uniform symmetric conclusion through an arbitrary group
equivalence. -/
theorem allChiefSeries_zero_of_symmetric_equiv
    {G : Type} [Group G] [Finite G] (n : ℕ) (hn : 5 ≤ n)
    (e : G ≃* Equiv.Perm (Fin n)) (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c = 0 := by
  have h := naturalSymmetric_allChiefSeries_zero n hn
    (actualChiefSeriesComap e.symm c)
  rwa [actualChiefSeriesComap_weight] at h

end SymmetricSubgroupAsymptotics

end
