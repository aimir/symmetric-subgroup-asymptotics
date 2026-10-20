import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators

/-!
# Socle generators from a finite cover of the normal lattice by chains

A cover by `t` chains bounds the number of distinct minimal normal subgroups
by `t`. Choosing one nonidentity element in each occupied chain therefore
normally generates the socle. The cover descends along surjections, giving
the same bound for every quotient without enumerating quotient socles.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A finite chain cover; no disjointness or computable choice is required. -/
structure NormalSubgroupChainCover (G : Type) [Group G] (t : ℕ) where
  carrier : Fin t → Subgroup G → Prop
  covers : ∀ N : Subgroup G, N.Normal → ∃ i, carrier i N
  comparable : ∀ i N M, N.Normal → M.Normal →
    carrier i N → carrier i M → N ≤ M ∨ M ≤ N

namespace NormalSubgroupChainCover

variable {G H : Type} [Group G] [Group H] {t : ℕ}

/-- A finite list of monotone chains supplies the semantic cover. -/
def ofFiniteChains {k : ℕ} (state : Fin t → Fin k → Subgroup G)
    (hmono : ∀ i, Monotone (state i))
    (hcover : ∀ N : Subgroup G, N.Normal → ∃ i j, state i j = N) :
    NormalSubgroupChainCover G t where
  carrier i N := ∃ j, state i j = N
  covers := hcover
  comparable i N M _ _ hi hj := by
    obtain ⟨a, rfl⟩ := hi
    obtain ⟨b, rfl⟩ := hj
    exact (le_total a b).elim
      (fun h ↦ Or.inl (hmono i h)) (fun h ↦ Or.inr (hmono i h))

/-- The inverse-image map transfers a normal-chain cover through a surjection. -/
def ofSurjective (D : NormalSubgroupChainCover G t)
    (f : G →* H) (hf : Function.Surjective f) : NormalSubgroupChainCover H t where
  carrier i N := D.carrier i (N.comap f)
  covers N hN := D.covers (N.comap f) (hN.comap f)
  comparable i N M hN hM hi hj := by
    rcases D.comparable i (N.comap f) (M.comap f)
        (hN.comap f) (hM.comap f) hi hj with h | h
    · left
      simpa only [Subgroup.map_comap_eq_self_of_surjective hf] using
        (Subgroup.map_mono (f := f) h)
    · right
      simpa only [Subgroup.map_comap_eq_self_of_surjective hf] using
        (Subgroup.map_mono (f := f) h)

/-- One generator per occupied chain suffices; empty chains contribute identity. -/
theorem socleBound (D : NormalSubgroupChainCover G t) :
    SocleNormalGeneratorBound G t := by
  let P (i : Fin t) (x : G) : Prop :=
    (∃ N : Subgroup G, IsMinimalNormalSubgroup N ∧ D.carrier i N ∧
      x ∈ N ∧ x ≠ 1) ∨
    (¬ ∃ N : Subgroup G, IsMinimalNormalSubgroup N ∧ D.carrier i N) ∧ x = 1
  have hex (i : Fin t) : ∃ x, P i x := by
    by_cases h : ∃ N : Subgroup G, IsMinimalNormalSubgroup N ∧ D.carrier i N
    · obtain ⟨N, hN, hi⟩ := h
      obtain ⟨x, hx, hxne⟩ := N.bot_or_exists_ne_one.resolve_left hN.2.1
      exact ⟨x, Or.inl ⟨N, hN, hi, hx, hxne⟩⟩
    · exact ⟨1, Or.inr ⟨h, rfl⟩⟩
  choose x hx using hex
  refine ⟨x, le_antisymm ?_ ?_⟩
  · apply Subgroup.normalClosure_le_normal
    rintro y ⟨i, rfl⟩
    rcases hx i with ⟨N, hN, _, hi, _⟩ | ⟨_, hi⟩
    · exact Subgroup.subset_normalClosure ⟨N, hN, hi⟩
    · rw [hi]
      exact one_mem _
  · apply Subgroup.normalClosure_le_normal
    rintro y ⟨N, hN, hy⟩
    obtain ⟨i, hi⟩ := D.covers N hN.1
    rcases hx i with ⟨M, hM, hj, hxM, hxne⟩ | ⟨hempty, _⟩
    · have hMN : M = N := by
        rcases D.comparable i M N hM.1 hN.1 hj hi with h | h
        · exact hN.2.2 M hM.1 hM.2.1 h
        · exact (hM.2.2 N hN.1 hN.2.1 h).symm
      have hxN : x i ∈ N := hMN ▸ hxM
      let K := Subgroup.normalClosure ({x i} : Set G)
      have hKN : K ≤ N := by
        letI := hN.1
        apply Subgroup.normalClosure_le_normal
        intro z hz
        exact (Set.mem_singleton_iff.mp hz) ▸ hxN
      have hKne : K ≠ ⊥ := by
        intro hbot
        apply hxne
        apply Subgroup.mem_bot.mp
        rw [← hbot]
        exact Subgroup.subset_normalClosure (Set.mem_singleton _)
      have hKeq : K = N := hN.2.2 K inferInstance hKne hKN
      have hKC : K ≤ Subgroup.normalClosure (Set.range x) :=
        Subgroup.normalClosure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self i))
      exact hKC (hKeq.symm ▸ hy)
    · exact (hempty ⟨N, hN, hi⟩).elim

/-- The same chain cover bounds every literal normal quotient. -/
theorem quotientSocleBound (D : NormalSubgroupChainCover G t)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) t :=
  (D.ofSurjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).socleBound

end NormalSubgroupChainCover
end SymmetricSubgroupAsymptotics

end
