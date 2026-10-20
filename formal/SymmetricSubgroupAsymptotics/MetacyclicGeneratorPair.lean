import SymmetricSubgroupAsymptotics.MetacyclicNormalGenerators

/-! A two-generator group is metacyclic when conjugation by the second
generator and its inverse preserve the cyclic subgroup of the first.
The normal subgroup and quotient in this proof are the literal ones. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem zpowers_normal_of_generating_pair
    {G : Type} [Group G] (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hba : b * a * b⁻¹ ∈ Subgroup.zpowers a)
    (hbia : b⁻¹ * a * b ∈ Subgroup.zpowers a) : (Subgroup.zpowers a).Normal := by
  let K := Subgroup.zpowers a
  have hfwd : K ≤ K.comap (MulAut.conj b).toMonoidHom := Subgroup.zpowers_le.mpr hba
  have hback : K ≤ K.comap (MulAut.conj b⁻¹).toMonoidHom := by
    apply Subgroup.zpowers_le.mpr
    change b⁻¹ * a * (b⁻¹)⁻¹ ∈ Subgroup.zpowers a
    simpa only [inv_inv] using hbia
  have hbn : b ∈ Subgroup.normalizer (K : Set G) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · exact fun hx ↦ hfwd hx
    · intro hx
      have hh := hback hx
      change b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ ∈ K at hh
      simpa [mul_assoc] using hh
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]
    exact (Subgroup.le_normalizer (H := K)) (Subgroup.mem_zpowers a)
  · rw [hg]
    exact hbn

theorem quotient_isCyclic_of_generating_pair
    {G : Type} [Group G] (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    [(Subgroup.zpowers a).Normal] : IsCyclic (G ⧸ Subgroup.zpowers a) := by
  let π := QuotientGroup.mk' (Subgroup.zpowers a)
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨π b, top_unique ?_⟩
  have hle : (⊤ : Subgroup G) ≤ (Subgroup.zpowers (π b)).comap π := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      change π a ∈ Subgroup.zpowers (π b)
      have ha : π a = 1 := (QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_zpowers a)
      rw [ha]
      exact (Subgroup.zpowers (π b)).one_mem
    · rw [hg]
      exact Subgroup.mem_zpowers (π b)
  intro q _hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers a) q
  exact hle (Subgroup.mem_top g)

theorem normal_generating_pairs_of_generating_pair_cyclic_conjugates
    {G : Type} [Group G] [Finite G] (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hba : b * a * b⁻¹ ∈ Subgroup.zpowers a)
    (hbia : b⁻¹ * a * b ∈ Subgroup.zpowers a) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 2 → G, Subgroup.normalClosure (Set.range x) = N := by
  letI := zpowers_normal_of_generating_pair a b hgen hba hbia
  letI := quotient_isCyclic_of_generating_pair a b hgen
  let π := QuotientGroup.mk' (Subgroup.zpowers a)
  letI : IsCyclic π.ker := by
    change IsCyclic (QuotientGroup.mk' (Subgroup.zpowers a)).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  exact normal_generating_pairs_of_cyclic_kernel π

theorem closure_pair_subtype_generators
    {G : Type} [Group G] (a b : G) :
    Subgroup.closure
      ({(⟨a, Subgroup.subset_closure (by simp)⟩ : Subgroup.closure ({a, b} : Set G)),
        ⟨b, Subgroup.subset_closure (by simp)⟩} :
        Set (Subgroup.closure ({a, b} : Set G))) = ⊤ := by
  have hset : ((↑) : Subgroup.closure ({a, b} : Set G) → G) ⁻¹' ({a, b} : Set G) =
      ({(⟨a, Subgroup.subset_closure (by simp)⟩ : Subgroup.closure ({a, b} : Set G)),
        ⟨b, Subgroup.subset_closure (by simp)⟩} :
        Set (Subgroup.closure ({a, b} : Set G))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
  simpa only [hset] using (Subgroup.closure_closure_coe_preimage (k := ({a, b} : Set G)))

/-- Direct adapter for literal generator closures. Only the two displayed
conjugation identities remain to be checked in the original action. -/
theorem normal_generating_pairs_closure_of_conjugate_powers
    {G : Type} [Group G] [Finite G] (a b : G) (k l : ℕ)
    (hba : b * a * b⁻¹ = a ^ k) (hbia : b⁻¹ * a * b = a ^ l) :
    ∀ N : Subgroup (Subgroup.closure ({a, b} : Set G)), N.Normal →
      ∃ x : Fin 2 → Subgroup.closure ({a, b} : Set G),
        Subgroup.normalClosure (Set.range x) = N := by
  let R := Subgroup.closure ({a, b} : Set G)
  let aR : R := ⟨a, Subgroup.subset_closure (by simp)⟩
  let bR : R := ⟨b, Subgroup.subset_closure (by simp)⟩
  apply normal_generating_pairs_of_generating_pair_cyclic_conjugates aR bR
    (closure_pair_subtype_generators a b)
  · have h : bR * aR * bR⁻¹ = aR ^ k := Subtype.ext hba
    rw [h]
    exact Subgroup.npow_mem_zpowers aR k
  · have h : bR⁻¹ * aR * bR = aR ^ l := Subtype.ext hbia
    rw [h]
    exact Subgroup.npow_mem_zpowers aR l

end SymmetricSubgroupAsymptotics

end
