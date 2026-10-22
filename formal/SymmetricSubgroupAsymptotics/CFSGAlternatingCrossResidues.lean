import SymmetricSubgroupAsymptotics.CFSGAlternatingCrossJoin
import SymmetricSubgroupAsymptotics.CFSGAlternatingSumTransitivity
import SymmetricSubgroupAsymptotics.CFSGActionSubgroupMove

/-! Actual two-conjugate Sylow generation for two and three outsiders.
The selected cross seed connects the first two outsiders. In the three-point
case the last outsider cannot remain a fixed point of the actual Sylow. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingCrossResidues
open CFSGAlternatingCyclicReflection CFSGAlternatingSumSupport
open CFSGAlternatingCrossSeed CFSGAlternatingCrossJoin CFSGAlternatingSumTransitivity
open CFSGPermutationCrossSwapWords

theorem cross_zero_image (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) :
    q k r hr (Sum.inr ⟨0, by omega⟩) = Sum.inl 4 := by
  simp [q, doubleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]

theorem cross_one_image (k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) :
    q k r hr (Sum.inr ⟨1, by omega⟩) = Sum.inl (-1) := by
  simp [q, doubleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff,
    four_ne_neg_one k hk, Ne.symm (four_ne_neg_one k hk)]

theorem exists_two_outsider_sylow_generation (k : ℕ) (hk : 2 ≤ k) :
    ∃ P : Sylow 2 (Alt k 2), join k 2 P = ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_seed k 2 hk (by decide)
  have hp := hP (Subgroup.subset_closure (show p k 2 ∈
    ({p k 2, q k 2 (by decide), a k 2} : Set (Equiv.Perm (X k 2))) by simp))
  have ha := hP (Subgroup.subset_closure (show a k 2 ∈
    ({p k 2, q k 2 (by decide), a k 2} : Set (Equiv.Perm (X k 2))) by simp))
  have hq := hP (Subgroup.subset_closure (show q k 2 (by decide) ∈
    ({p k 2, q k 2 (by decide), a k 2} : Set (Equiv.Perm (X k 2))) by simp))
  have hqK := rawSylow_le_rawJoin k 2 P hq
  letI : MulAction.IsPretransitive (rawJoin k 2 P) (X k 2) := by
    apply pretransitive_two k (rawJoin k 2 P) (rotation_mem_rawJoin k 2 P hp)
    intro i
    fin_cases i
    · exact ⟨⟨q k 2 (by decide), hqK⟩, 4, cross_zero_image k 2 hk (by decide)⟩
    · exact ⟨⟨q k 2 (by decide), hqK⟩, -1, cross_one_image k 2 hk (by decide)⟩
  exact ⟨P, join_eq_top_of_pretransitive k 2 hk (by omega) P hp ha⟩

theorem three_join_pretransitive (k : ℕ) (hk : 2 ≤ k) (P : Sylow 2 (Alt k 3))
    (K : Subgroup (Equiv.Perm (X k 3)))
    (hPK : (P : Subgroup (Alt k 3)).map (alternatingGroup (X k 3)).subtype ≤ K)
    (hg : g k 3 ∈ K) (hqK : q k 3 (by decide) ∈ K) :
    MulAction.IsPretransitive K (X k 3) := by
  have hsize : 3 ≤ Nat.card (X k 3) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, ZMod.card, Fintype.card_fin]
    omega
  have heven : 2 ∣ Nat.card (X k 3) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, ZMod.card, Fintype.card_fin]
    exact ⟨2 * k + 2, by omega⟩
  have hmove : ∃ h : K,
      (h : Equiv.Perm (X k 3)) (Sum.inr 2) ≠ Sum.inr 2 :=
    CFSGActionSubgroupMove.alternating_exists_move P K hPK hsize heven (Sum.inr 2)
  apply pretransitive_three k K hg _ hmove
  intro i
  fin_cases i
  · exact ⟨⟨q k 3 (by decide), hqK⟩, 4, cross_zero_image k 3 hk (by decide)⟩
  · exact ⟨⟨q k 3 (by decide), hqK⟩, -1, cross_one_image k 3 hk (by decide)⟩

theorem exists_three_outsider_sylow_generation (k : ℕ) (hk : 2 ≤ k) :
    ∃ P : Sylow 2 (Alt k 3), join k 3 P = ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_seed k 3 hk (by decide)
  have hp := hP (Subgroup.subset_closure (show p k 3 ∈
    ({p k 3, q k 3 (by decide), a k 3} : Set (Equiv.Perm (X k 3))) by simp))
  have ha := hP (Subgroup.subset_closure (show a k 3 ∈
    ({p k 3, q k 3 (by decide), a k 3} : Set (Equiv.Perm (X k 3))) by simp))
  have hq := hP (Subgroup.subset_closure (show q k 3 (by decide) ∈
    ({p k 3, q k 3 (by decide), a k 3} : Set (Equiv.Perm (X k 3))) by simp))
  letI := three_join_pretransitive k hk P (rawJoin k 3 P)
    (rawSylow_le_rawJoin k 3 P) (rotation_mem_rawJoin k 3 P hp)
    (rawSylow_le_rawJoin k 3 P hq)
  exact ⟨P, join_eq_top_of_pretransitive k 3 hk (by omega) P hp ha⟩

end SymmetricSubgroupAsymptotics.CFSGAlternatingCrossResidues
