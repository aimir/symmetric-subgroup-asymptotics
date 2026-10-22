import SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossJoin
import SymmetricSubgroupAsymptotics.CFSGAlternatingSumTransitivity
import SymmetricSubgroupAsymptotics.CFSGAlternatingJoinMoves

/-! The same actual length-five Sylow construction covers degrees seven
and eight. The extra outsider at degree eight is absorbed using the actual
Sylow no-fixed-point theorem. No exceptional subgroup classification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossResidues
open CFSGAlternatingCyclicReflection CFSGAlternatingCrossSeed CFSGAlternatingCrossJoin
open CFSGAlternatingSumTransitivity CFSGPermutationCrossSwapWords

theorem cross_zero_image (r : ℕ) (hr : 2 ≤ r) :
    CFSGAlternatingSmallCrossSeed.q r hr (Sum.inr ⟨0, by omega⟩) = Sum.inl 1 := by
  simp [CFSGAlternatingSmallCrossSeed.q, doubleSwap, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, Fin.ext_iff]

theorem cross_one_image (r : ℕ) (hr : 2 ≤ r) :
    CFSGAlternatingSmallCrossSeed.q r hr (Sum.inr ⟨1, by omega⟩) = Sum.inl 3 := by
  simp [CFSGAlternatingSmallCrossSeed.q, doubleSwap, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, show (3 : Cycle 1) ≠ 1 by decide]

theorem exists_seed_members (r : ℕ) (hr : 2 ≤ r) :
    ∃ P : Sylow 2 (Alt 1 r),
      CFSGAlternatingSmallCrossSeed.p r ∈
        (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype ∧
      CFSGAlternatingSmallCrossSeed.q r hr ∈
        (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype ∧
      CFSGAlternatingSmallCrossSeed.b r hr ∈
        (P : Subgroup (Alt 1 r)).map (alternatingGroup (X 1 r)).subtype := by
  obtain ⟨P, hP⟩ := CFSGAlternatingSmallCrossJoin.exists_sylow_seed r hr
  refine ⟨P, ?_, ?_, ?_⟩ <;> apply hP <;> apply Subgroup.subset_closure <;> simp

theorem two_join_pretransitive (P : Sylow 2 (Alt 1 2))
    (hp : CFSGAlternatingSmallCrossSeed.p 2 ∈
      (P : Subgroup (Alt 1 2)).map (alternatingGroup (X 1 2)).subtype)
    (hq : CFSGAlternatingSmallCrossSeed.q 2 (by decide) ∈
      (P : Subgroup (Alt 1 2)).map (alternatingGroup (X 1 2)).subtype) :
    MulAction.IsPretransitive (rawJoin 1 2 P) (X 1 2) := by
  have hqK := rawSylow_le_rawJoin 1 2 P hq
  apply pretransitive_two 1 (rawJoin 1 2 P) (CFSGAlternatingSmallCrossJoin.rotation_mem_rawJoin 2 P hp)
  intro i
  fin_cases i
  · exact ⟨⟨CFSGAlternatingSmallCrossSeed.q 2 (by decide), hqK⟩, 1, cross_zero_image 2 (by decide)⟩
  · exact ⟨⟨CFSGAlternatingSmallCrossSeed.q 2 (by decide), hqK⟩, 3, cross_one_image 2 (by decide)⟩

theorem three_join_pretransitive (P : Sylow 2 (Alt 1 3))
    (hp : CFSGAlternatingSmallCrossSeed.p 3 ∈
      (P : Subgroup (Alt 1 3)).map (alternatingGroup (X 1 3)).subtype)
    (hq : CFSGAlternatingSmallCrossSeed.q 3 (by decide) ∈
      (P : Subgroup (Alt 1 3)).map (alternatingGroup (X 1 3)).subtype) :
    MulAction.IsPretransitive (rawJoin 1 3 P) (X 1 3) := by
  have hqK := rawSylow_le_rawJoin 1 3 P hq
  have hsize : 3 ≤ Nat.card (X 1 3) := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_sum, ZMod.card]
  have heven : 2 ∣ Nat.card (X 1 3) := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_sum, ZMod.card]
  have hm : ∃ h : rawJoin 1 3 P, (h : Equiv.Perm (X 1 3)) (Sum.inr 2) ≠ Sum.inr 2 :=
    CFSGAlternatingJoinMoves.exists_move P (join 1 3 P)
      (fun _ hx => Subgroup.subset_closure (Or.inl hx)) hsize heven (Sum.inr 2)
  apply pretransitive_three 1 (rawJoin 1 3 P)
    (CFSGAlternatingSmallCrossJoin.rotation_mem_rawJoin 3 P hp) _ hm
  intro i
  fin_cases i
  · exact ⟨⟨CFSGAlternatingSmallCrossSeed.q 3 (by decide), hqK⟩, 1, cross_zero_image 3 (by decide)⟩
  · exact ⟨⟨CFSGAlternatingSmallCrossSeed.q 3 (by decide), hqK⟩, 3, cross_one_image 3 (by decide)⟩

theorem degree_seven_sylow_generation : ∃ P : Sylow 2 (Alt 1 2), join 1 2 P = ⊤ := by
  obtain ⟨P, hp, hq, hb⟩ := exists_seed_members 2 (by decide)
  letI := two_join_pretransitive P hp hq
  exact ⟨P, CFSGAlternatingSmallCrossJoin.join_eq_top_of_pretransitive 2 (by decide) (by decide) P hp hb⟩

theorem degree_eight_sylow_generation : ∃ P : Sylow 2 (Alt 1 3), join 1 3 P = ⊤ := by
  obtain ⟨P, hp, hq, hb⟩ := exists_seed_members 3 (by decide)
  letI := three_join_pretransitive P hp hq
  exact ⟨P, CFSGAlternatingSmallCrossJoin.join_eq_top_of_pretransitive 3 (by decide) (by decide) P hp hb⟩

end SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossResidues
