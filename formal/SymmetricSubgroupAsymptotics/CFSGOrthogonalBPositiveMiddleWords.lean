import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveRadicalWords

/-! Actual positive short-root words realize every middle-coordinate
functional while preserving ALL negative coordinates and fixing V⁺
pointwise. This applies to arbitrary vectors, not only negative-zero
vectors, and supports literal opposed-space normalization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveMiddleWords
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortMembership
open CFSGOrthogonalBVectorCoordinates
variable (K : Type) [Field K]

def negativeDot (n : ℕ) (a : Fin n → K) (v : Index n → K) : K :=
  ∑ i, a i * v (neg n i)

def realizedParameters (n : ℕ) : AddSubmonoid (Fin n → K) where
  carrier := {a | ∃ g : elementaryRootGroup K n,
    (∀ v : Index n → K, ∀ i, (((g.val : Mat K n) *ᵥ v) (neg n i)) = v (neg n i)) ∧
    (∀ v : Index n → K, (((g.val : Mat K n) *ᵥ v) (middle n)) =
      v (middle n) - 2 * negativeDot K n a v) ∧
    (∀ v ∈ positiveSubspace K n, (g.val : Mat K n) *ᵥ v = v)}
  zero_mem' := by
    refine ⟨1, ?_, ?_, ?_⟩
    · intro v i; simp
    · intro v; simp [negativeDot]
    · intro v _; simp
  add_mem' := by
    rintro a b ⟨g, hgn, hgm, hgf⟩ ⟨h, hhn, hhm, hhf⟩
    refine ⟨g * h, ?_, ?_, ?_⟩
    · intro v i
      change (((g.val : Mat K n) * (h.val : Mat K n)) *ᵥ v) (neg n i) = _
      rw [← Matrix.mulVec_mulVec, hgn, hhn]
    · intro v
      change (((g.val : Mat K n) * (h.val : Mat K n)) *ᵥ v) (middle n) = _
      rw [← Matrix.mulVec_mulVec, hgm, hhm]
      have hdot : negativeDot K n a ((h.val : Mat K n) *ᵥ v) = negativeDot K n a v := by
        simp only [negativeDot, hhn]
      have hadd : negativeDot K n (a + b) v = negativeDot K n a v + negativeDot K n b v := by
        simp [negativeDot, add_mul, Finset.sum_add_distrib]
      rw [hdot, hadd]
      ring
    · intro v hv
      change ((g.val : Mat K n) * (h.val : Mat K n)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, hhf v hv, hgf v hv]

theorem single_realized (s : ℕ) (i : Fin (s + 1)) (a : K) :
    Pi.single i a ∈ realizedParameters K (s + 1) := by
  let g : elementaryRootGroup K (s + 1) :=
    ⟨shortUnit K (s + 1) (Sum.inl i) a, shortUnit_mem K s (Sum.inl i) a⟩
  have hg (v : Index (s + 1) → K) := shortUnit_vector_action K (s + 1) (Sum.inl i) a v
  refine ⟨g, ?_, ?_, ?_⟩
  · intro v j
    change ((shortUnit K (s + 1) (Sum.inl i) a : Mat K (s + 1)) *ᵥ v) (neg (s + 1) j) = _
    rw [hg]
    simp [neg, middle]
  · intro v
    change ((shortUnit K (s + 1) (Sum.inl i) a : Mat K (s + 1)) *ᵥ v) (middle (s + 1)) = _
    rw [hg]
    simp [negativeDot, paired, middle, neg, Pi.single_apply]
    ring
  · intro v hv
    obtain ⟨hn, hm⟩ := (mem_positiveSubspace K (s + 1) v).mp hv
    change (shortUnit K (s + 1) (Sum.inl i) a : Mat K (s + 1)) *ᵥ v = v
    rw [hg]
    have hz : v (Sum.inl (paired (s + 1) (Sum.inl i))) = 0 := hn i
    simp only [hz, hm, mul_zero, sub_self, zero_smul, add_zero]

theorem exists_middle_word (s : ℕ) (a : Fin (s + 1) → K) :
    ∃ g : elementaryRootGroup K (s + 1),
      (∀ v : Index (s + 1) → K, ∀ i,
        (((g.val : Mat K (s + 1)) *ᵥ v) (neg (s + 1) i)) = v (neg (s + 1) i)) ∧
      (∀ v : Index (s + 1) → K,
        (((g.val : Mat K (s + 1)) *ᵥ v) (middle (s + 1))) =
          v (middle (s + 1)) - 2 * negativeDot K (s + 1) a v) ∧
      (∀ v ∈ positiveSubspace K (s + 1), (g.val : Mat K (s + 1)) *ᵥ v = v) := by
  change a ∈ realizedParameters K (s + 1)
  rw [← Finset.univ_sum_single a]
  exact (realizedParameters K (s + 1)).sum_mem (fun i _ => single_realized K s i (a i))

theorem functional_coordinates {n : ℕ} (l : (Fin n → K) →ₗ[K] K) (y : Fin n → K) :
    l y = ∑ i, y i * l (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : Pi.single i (y i) = y i • (Pi.single i 1 : Fin n → K) := by
    funext j
    by_cases hj : j = i <;> simp [Pi.single_apply, hj]
  rw [he, map_smul, smul_eq_mul]

theorem exists_clear_middle_functional (h2 : (2 : K) ≠ 0) (s : ℕ)
    (l : (Fin (s + 1) → K) →ₗ[K] K) :
    ∃ g : elementaryRootGroup K (s + 1),
      (∀ v : Index (s + 1) → K, ∀ i,
        (((g.val : Mat K (s + 1)) *ᵥ v) (neg (s + 1) i)) = v (neg (s + 1) i)) ∧
      (∀ v : Index (s + 1) → K, v (middle (s + 1)) = l (negativePart K (s + 1) v) →
        (((g.val : Mat K (s + 1)) *ᵥ v) (middle (s + 1))) = 0) ∧
      (∀ v ∈ positiveSubspace K (s + 1), (g.val : Mat K (s + 1)) *ᵥ v = v) := by
  let a : Fin (s + 1) → K := fun i => l (Pi.single i 1) / 2
  obtain ⟨g, hgn, hgm, hgf⟩ := exists_middle_word K s a
  refine ⟨g, hgn, ?_, hgf⟩
  intro v hv
  have hd : 2 * negativeDot K (s + 1) a v = l (negativePart K (s + 1) v) := by
    rw [negativeDot, Finset.mul_sum, functional_coordinates K]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a, negativePart]
    field_simp [h2]
  rw [hgm, hd, hv, sub_self]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveMiddleWords
