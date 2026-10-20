import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-!
# Normal generators across a kernel contained in every nontrivial normal

For an epimorphism whose kernel lies in every nontrivial normal subgroup,
a positive uniform normal-generator bound on the target lifts unchanged.
The kernel itself is normally cyclic. No splitting or finite normal table
is required; the kernel is retained as the kernel of the displayed map.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuples_of_kernel_normal_cover
    {G Q : Type} [Group G] [Group Q]
    (π : G →* Q) (hπ : Function.Surjective π)
    (d : G) (hd : d ∈ π.ker) (hd1 : d ≠ 1)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → π.ker ≤ N)
    {t : ℕ} (ht : 0 < t)
    (hQ : ∀ M : Subgroup Q, M.Normal →
      ∃ x : Fin t → Q, Subgroup.normalClosure (Set.range x) = M) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin t → G, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  by_cases hNb : N = ⊥
  · refine ⟨fun _ ↦ 1, ?_⟩
    rw [hNb]
    apply le_antisymm _ bot_le
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact one_mem _
  by_cases hMb : N.map π = ⊥
  · have hNK : N = π.ker := by
      apply le_antisymm _ (hcover N hN hNb)
      intro n hn
      exact Subgroup.mem_bot.mp (hMb ▸ (show π n ∈ N.map π from ⟨n, hn, rfl⟩))
    let x : Fin t → G := fun _ ↦ d
    let L := Subgroup.normalClosure (Set.range x)
    letI : L.Normal := by dsimp [L]; infer_instance
    have hLK : L ≤ π.ker := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨i, rfl⟩
      exact hd
    have hLb : L ≠ ⊥ := by
      intro h
      apply hd1
      apply Subgroup.mem_bot.mp
      rw [← h]
      exact Subgroup.subset_normalClosure ⟨(⟨0, ht⟩ : Fin t), rfl⟩
    refine ⟨x, ?_⟩
    change L = N
    exact (le_antisymm hLK (hcover L inferInstance hLb)).trans hNK.symm
  · obtain ⟨x, hx⟩ := hQ (N.map π) (hN.map π hπ)
    have hlift : ∀ i, ∃ y : G, y ∈ N ∧ π y = x i := by
      intro i
      have hxi : x i ∈ N.map π := by
        rw [← hx]
        exact Subgroup.subset_normalClosure (Set.mem_range_self i)
      exact hxi
    choose y hy hπy using hlift
    let L := Subgroup.normalClosure (Set.range y)
    letI : L.Normal := by dsimp [L]; infer_instance
    have hLN : L ≤ N := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨i, rfl⟩
      exact hy i
    have himage : π '' Set.range y = Set.range x := by
      ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hπy i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨y i, Set.mem_range_self i, hπy i⟩
    have hmap : L.map π = N.map π := by
      dsimp [L]
      rw [Subgroup.map_normalClosure _ _ hπ, himage]
      exact hx
    have hLb : L ≠ ⊥ := by
      intro h
      apply hMb
      rw [← hmap, h, Subgroup.map_bot]
    have hkerL : π.ker ≤ L := hcover L inferInstance hLb
    refine ⟨y, ?_⟩
    change L = N
    calc
      L = (L.map π).comap π := (Subgroup.comap_map_eq_self hkerL).symm
      _ = (N.map π).comap π := by rw [hmap]
      _ = N := Subgroup.comap_map_eq_self (hkerL.trans hLN)

theorem quotientSocle_of_kernel_normal_cover
    {G Q : Type} [Group G] [Group Q]
    (π : G →* Q) (hπ : Function.Surjective π)
    (d : G) (hd : d ∈ π.ker) (hd1 : d ≠ 1)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → π.ker ≤ N)
    {t : ℕ} (ht : 0 < t)
    (hQ : ∀ M : Subgroup Q, M.Normal →
      ∃ x : Fin t → Q, Subgroup.normalClosure (Set.range x) = M)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) t :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples_of_kernel_normal_cover π hπ d hd hd1 hcover ht hQ) N

end SymmetricSubgroupAsymptotics

end
