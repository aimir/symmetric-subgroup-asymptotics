import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveSubspace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FieldSimp

/-! Actual short-root words realize every translation on the subspace
with all negative coordinates zero. In particular they clear a middle
column while fixing the entire original positive singular subspace. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveRadicalWords
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortMembership
open CFSGOrthogonalBVectorCoordinates
variable (K : Type) [Field K]

def realizedParameters (n : ℕ) : AddSubmonoid (Fin n → K) where
  carrier := {a | ∃ g : elementaryRootGroup K n, ∀ v : Index n → K,
    (∀ i, v (neg n i) = 0) →
      (g.val : Mat K n) *ᵥ v = v + v (middle n) • positiveEmbedding K n a}
  zero_mem' := by
    refine ⟨1, ?_⟩
    intro v _
    simp
  add_mem' := by
    rintro a b ⟨g, hg⟩ ⟨h, hh⟩
    refine ⟨g * h, ?_⟩
    intro v hn
    have hv := hh v hn
    have hn' : ∀ i, (((h.val : Mat K n) *ᵥ v) (neg n i)) = 0 := by
      intro i
      rw [hv]
      simpa [positiveEmbedding, neg] using hn i
    have hm : (((h.val : Mat K n) *ᵥ v) (middle n)) = v (middle n) := by
      rw [hv]
      simp [positiveEmbedding, middle]
    change ((g.val : Mat K n) * (h.val : Mat K n)) *ᵥ v = _
    rw [← Matrix.mulVec_mulVec, hg _ hn', hm, hv, map_add, smul_add]
    abel

theorem single_realized (s : ℕ) (i : Fin (s + 1)) (a : K) :
    Pi.single i a ∈ realizedParameters K (s + 1) := by
  refine ⟨⟨shortUnit K (s + 1) (Sum.inl i) a,
    shortUnit_mem K s (Sum.inl i) a⟩, ?_⟩
  intro v hn
  change (shortUnit K (s + 1) (Sum.inl i) a : Mat K (s + 1)) *ᵥ v = _
  rw [shortUnit_vector_action]
  have hz : v (Sum.inl (paired (s + 1) (Sum.inl i))) = 0 := hn i
  rw [hz]
  simp only [mul_zero, sub_zero, zero_smul, add_zero]
  have he : positiveEmbedding K (s + 1) (Pi.single i a) =
      a • (Pi.single (pos (s + 1) i) 1 : Index (s + 1) → K) := by
    funext j
    rcases j with (j | j) | j
    · simp [positiveEmbedding, pos, Pi.single_apply]
    · simp [positiveEmbedding, pos, Pi.single_apply]
    · cases j
      simp [positiveEmbedding, pos, Pi.single_apply]
  rw [he, smul_smul, mul_comm a]

theorem exists_positive_translation (s : ℕ) (a : Fin (s + 1) → K) :
    ∃ g : elementaryRootGroup K (s + 1), ∀ v : Index (s + 1) → K,
      (∀ i, v (neg (s + 1) i) = 0) →
        (g.val : Mat K (s + 1)) *ᵥ v =
          v + v (middle (s + 1)) • positiveEmbedding K (s + 1) a := by
  change a ∈ realizedParameters K (s + 1)
  rw [← Finset.univ_sum_single a]
  exact (realizedParameters K (s + 1)).sum_mem (fun i _ => single_realized K s i (a i))

theorem exists_clear_positive (s : ℕ) (v : Index (s + 1) → K)
    (hn : ∀ i, v (neg (s + 1) i) = 0) (hm : v (middle (s + 1)) ≠ 0) :
    ∃ g : elementaryRootGroup K (s + 1),
      (∀ u ∈ positiveSubspace K (s + 1), (g.val : Mat K (s + 1)) *ᵥ u = u) ∧
      (g.val : Mat K (s + 1)) *ᵥ v =
        v (middle (s + 1)) • Pi.single (middle (s + 1)) 1 := by
  let a : Fin (s + 1) → K := fun i => -(v (pos (s + 1) i)) / v (middle (s + 1))
  obtain ⟨g, hg⟩ := exists_positive_translation K s a
  refine ⟨g, ?_, ?_⟩
  · intro u hu
    obtain ⟨hun, hum⟩ := (mem_positiveSubspace K (s + 1) u).mp hu
    rw [hg u hun, hum, zero_smul, add_zero]
  · rw [hg v hn]
    funext i
    rcases i with (i | i) | i
    · simp only [Pi.add_apply, Pi.smul_apply, positiveEmbedding, Sum.elim_inl,
        pos, smul_eq_mul, Pi.single_apply, Sum.inl_ne_inr, if_false, mul_zero]
      dsimp [a]
      field_simp [hm]
      ring
    · simpa [positiveEmbedding, neg, middle, Pi.single_apply] using hn i
    · cases i
      simp [positiveEmbedding, middle, Pi.single_apply]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveRadicalWords
