import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-! The first, purely group-theoretic half of RDT Lemma 8.5.
A minimal normal subgroup has trivial or minimal normal image under an
ACTUAL surjection. This does not assume solubility or a socle bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.SocleSurjectiveImage

variable {G H : Type} [Group G] [Group H]

/-- Pulling a normal subgroup of the image back INSIDE the same M proves
minimality; the original ambient normality is retained. -/
theorem minimalNormal_map (f : G →* H) (hf : Function.Surjective f)
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hne : M.map f ≠ ⊥) : IsMinimalNormalSubgroup (M.map f) := by
  refine ⟨hM.1.map f hf,hne,?_⟩
  intro N hN hNne hNM
  let L : Subgroup G := M ⊓ N.comap f
  letI : M.Normal := hM.1
  letI : N.Normal := hN
  have hLnormal : L.Normal := inferInstance
  have hmap : L.map f = N := by
    apply le_antisymm
    · rintro z ⟨x,hx,rfl⟩
      exact hx.2
    · intro z hz
      obtain ⟨x,hx,hfx⟩ := hNM hz
      refine ⟨x,⟨hx,?_⟩,hfx⟩
      change f x ∈ N
      simpa only [hfx] using hz
  have hLne : L ≠ ⊥ := by
    intro he
    apply hNne
    rw [← hmap,he,Subgroup.map_bot]
  have hLM : L = M := hM.2.2 L hLnormal hLne inf_le_left
  exact hmap.symm.trans (congrArg (Subgroup.map f) hLM)

/-- Every literal socle maps into the target socle under a surjection. -/
theorem socle_le_comap (f : G →* H) (hf : Function.Surjective f) :
    finiteGroupSocle G ≤ (finiteGroupSocle H).comap f := by
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨M,hM,hx⟩
  change f x ∈ finiteGroupSocle H
  by_cases he : M.map f = ⊥
  · have hm : f x ∈ M.map f := ⟨x,hx,rfl⟩
    rw [he] at hm
    have hone : f x = 1 := hm
    simpa only [hone] using (finiteGroupSocle H).one_mem
  · exact Subgroup.subset_normalClosure
      ⟨M.map f,minimalNormal_map f hf M hM he,⟨x,hx,rfl⟩⟩

end SymmetricSubgroupAsymptotics.MarkedC4.SocleSurjectiveImage
