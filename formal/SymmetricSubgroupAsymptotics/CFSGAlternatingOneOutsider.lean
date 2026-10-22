import SymmetricSubgroupAsymptotics.CFSGAlternatingCrossJoin
import SymmetricSubgroupAsymptotics.CFSGAlternatingFiveCycleGeneration
import SymmetricSubgroupAsymptotics.CFSGAlternatingSumTransitivity
import SymmetricSubgroupAsymptotics.CFSGActionSubgroupMove

/-! One-outsider Sylow generation, including degree six. The length-five
base uses two explicit five-point involution identities; larger cycles use
the uniform checked identities. Even total degree prevents a common fixed
outsider, and actual supported alternating generation completes the proof. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingOneOutsider
open CFSGAlternatingCyclicReflection CFSGAlternatingCyclicDoubleSwap
open CFSGAlternatingSumSupport CFSGAlternatingCrossSeed CFSGAlternatingCrossJoin

theorem adjacent_square_of_positive (k : ℕ) (hk : 1 ≤ k) : adjacentDoubleSwap k ^ 2 = 1 := by
  by_cases h : 2 ≤ k
  · exact CFSGAlternatingCyclicSylowGeneration.adjacentDoubleSwap_square k h
  · have he : k = 1 := by omega
    subst k
    decide +kernel

theorem adjacent_reflection_commute_of_positive (k : ℕ) (hk : 1 ≤ k) :
    Commute (adjacentDoubleSwap k) (reflection k) := by
  by_cases h : 2 ≤ k
  · exact CFSGAlternatingCyclicSylowGeneration.adjacentDoubleSwap_commute_reflection k h
  · have he : k = 1 := by omega
    subst k
    change adjacentDoubleSwap 1 * reflection 1 = reflection 1 * adjacentDoubleSwap 1
    apply Equiv.ext
    intro x
    fin_cases x <;> decide +kernel

theorem cycle_alternating_le (k : ℕ) (hk : 1 ≤ k)
    (H : Subgroup (Equiv.Perm (Cycle k)))
    (hg : rotation k ∈ H) (ha : adjacentDoubleSwap k ∈ H) : alternatingGroup (Cycle k) ≤ H := by
  by_cases h : 2 ≤ k
  · exact alternating_le_of_rotation_doubleSwap k h H hg ha
  · have he : k = 1 := by omega
    subst k
    exact CFSGAlternatingFiveCycleGeneration.alternating_le_of_five_rotation_doubleSwap H hg ha

def seed (k : ℕ) : Subgroup (Equiv.Perm (X k 1)) :=
  Subgroup.closure ({p k 1, (1 : Equiv.Perm (X k 1)), a k 1} :
    Set (Equiv.Perm (X k 1)))

theorem seed_isPGroup (k : ℕ) (hk : 1 ≤ k) : IsPGroup 2 (seed k) := by
  apply CFSGDihedralTwoGroupWords.closure_three_involutions_isPGroup
  · change extensionHom (Cycle k) 1 (reflection k) ^ 2 = 1
    rw [← map_pow, reflection_square, map_one]
  · simp
  · change extensionHom (Cycle k) 1 (adjacentDoubleSwap k) ^ 2 = 1
    rw [← map_pow, adjacent_square_of_positive k hk, map_one]
  · rw [mul_one, show (4 : ℕ) = 2 * 2 by decide, pow_mul]
    change (extensionHom (Cycle k) 1 (reflection k) ^ 2) ^ 2 = 1
    rw [← map_pow, reflection_square, map_one, one_pow]
  · exact (adjacent_reflection_commute_of_positive k hk).map (extensionHom (Cycle k) 1)
  · exact Commute.one_right _

theorem seed_le_alternating (k : ℕ) (hk : 1 ≤ k) :
    seed k ≤ alternatingGroup (X k 1) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · subst x
    exact extension_even (Cycle k) 1 (reflection k)
      (Equiv.Perm.mem_alternatingGroup.mpr (reflection_even k))
  · subst x; exact (alternatingGroup (X k 1)).one_mem
  · subst x
    exact extension_even (Cycle k) 1 (adjacentDoubleSwap k) (adjacentDoubleSwap_even k hk)

theorem exists_sylow_seed (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Sylow 2 (Alt k 1),
      seed k ≤ (P : Subgroup (Alt k 1)).map (alternatingGroup (X k 1)).subtype := by
  have heven := seed_le_alternating k hk
  obtain ⟨P, hP⟩ := ((seed_isPGroup k hk).comap_of_injective
    (alternatingGroup (X k 1)).subtype
    (alternatingGroup (X k 1)).subtype_injective).exists_le_sylow
  refine ⟨P, ?_⟩
  intro x hx
  exact ⟨⟨x, heven hx⟩, hP hx, rfl⟩

theorem join_pretransitive (k : ℕ) (hk : 1 ≤ k) (P : Sylow 2 (Alt k 1))
    (K : Subgroup (Equiv.Perm (X k 1)))
    (hPK : (P : Subgroup (Alt k 1)).map (alternatingGroup (X k 1)).subtype ≤ K)
    (hg : g k 1 ∈ K) : MulAction.IsPretransitive K (X k 1) := by
  have hsize : 3 ≤ Nat.card (X k 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, ZMod.card, Fintype.card_fin]
    omega
  have hd : 2 ∣ Nat.card (X k 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, ZMod.card, Fintype.card_fin]
    exact ⟨2 * k + 1, by omega⟩
  exact CFSGAlternatingSumTransitivity.pretransitive_one k K hg
    (CFSGActionSubgroupMove.alternating_exists_move P K hPK hsize hd (Sum.inr 0))

theorem join_eq_top (k : ℕ) (hk : 1 ≤ k) (P : Sylow 2 (Alt k 1))
    (hp : p k 1 ∈ (P : Subgroup (Alt k 1)).map (alternatingGroup (X k 1)).subtype)
    (ha : a k 1 ∈ (P : Subgroup (Alt k 1)).map (alternatingGroup (X k 1)).subtype) :
    join k 1 P = ⊤ := by
  letI := join_pretransitive k hk P (rawJoin k 1 P)
    (rawSylow_le_rawJoin k 1 P) (rotation_mem_rawJoin k 1 P hp)
  have hfull : alternatingGroup (X k 1) ≤ rawJoin k 1 P := by
    apply alternating_le_of_transitive_extension (Cycle k) 1 (rawJoin k 1 P)
    · rw [ZMod.card]; omega
    · rw [ZMod.card]; omega
    · intro b
      have hc : alternatingGroup (Cycle k) ≤
          (rawJoin k 1 P).comap (extensionHom (Cycle k) 1) := by
        apply cycle_alternating_le k hk _ (rotation_mem_rawJoin k 1 P hp)
        exact rawSylow_le_rawJoin k 1 P ha
      exact hc b.property
  apply (Subgroup.eq_top_iff' (join k 1 P)).mpr
  intro x
  obtain ⟨y, hy, he⟩ := hfull x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

theorem exists_one_outsider_sylow_generation (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Sylow 2 (Alt k 1), join k 1 P = ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_seed k hk
  have hp : p k 1 ∈ (P : Subgroup (Alt k 1)).map (alternatingGroup (X k 1)).subtype :=
    hP (Subgroup.subset_closure (by simp))
  have ha : a k 1 ∈ (P : Subgroup (Alt k 1)).map (alternatingGroup (X k 1)).subtype :=
    hP (Subgroup.subset_closure (by simp))
  exact ⟨P, join_eq_top k hk P hp ha⟩

end SymmetricSubgroupAsymptotics.CFSGAlternatingOneOutsider
