import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
import Mathlib.Data.Fin.Tuple.Basic

/-! Normal-generator bounds lift across an actual cyclic kernel.
For each ambient normal subgroup, one generator covers its intersection
with the kernel; lifts of normal generators of its image cover the rest.
No splitting, centrality, or census assumption is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuples_of_cyclic_kernel_normal_generators
    {G Q : Type} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) [IsCyclic f.ker]
    {t : ℕ}
    (hQ : ∀ M : Subgroup Q, M.Normal →
      ∃ y : Fin t → Q, Subgroup.normalClosure (Set.range y) = M) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin (1 + t) → G, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  let ι : f.ker →* G := f.ker.subtype
  let K : Subgroup f.ker := N.comap ι
  obtain ⟨g, hg⟩ := K.isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic K)
  have hgK : g ∈ K := by rw [← hg]; exact Subgroup.mem_zpowers g
  obtain ⟨y, hy⟩ := hQ (N.map f) (hN.map f hf)
  have hlift : ∀ i, ∃ z : G, z ∈ N ∧ f z = y i := by
    intro i
    have hi : y i ∈ N.map f := by
      rw [← hy]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact hi
  choose z hzN hz using hlift
  let u : Fin (1 + t) → G := Fin.addCases (fun _ ↦ ι g) z
  let L := Subgroup.normalClosure (Set.range u)
  letI : L.Normal := by dsimp [L]; infer_instance
  have hgL : ι g ∈ L := by
    have hh := Subgroup.subset_normalClosure (Set.mem_range_self (f := u) ((0 : Fin 1).castAdd t))
    simpa only [u, Fin.addCases_left] using hh
  have hzL (i : Fin t) : z i ∈ L := by
    have hh := Subgroup.subset_normalClosure (Set.mem_range_self (f := u) (i.natAdd 1))
    simpa only [u, Fin.addCases_right] using hh
  have hLN : L ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [u, Fin.addCases_left] using hgK
    · intro j
      simpa only [u, Fin.addCases_right] using hzN j
  have hKL : K ≤ L.comap ι := by
    rw [← hg]
    exact Subgroup.zpowers_le.mpr hgL
  have hML : N.map f ≤ L.map f := by
    letI : (L.map f).Normal := (inferInstance : L.Normal).map f hf
    rw [← hy]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact ⟨z i, hzL i, hz i⟩
  refine ⟨u, le_antisymm hLN ?_⟩
  intro n hn
  obtain ⟨l, hl, heq⟩ := hML (show f n ∈ N.map f from ⟨n, hn, rfl⟩)
  have hker : n * l⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
  have hk : (⟨n * l⁻¹, hker⟩ : f.ker) ∈ K :=
    N.mul_mem hn (N.inv_mem (hLN hl))
  have hd : n * l⁻¹ ∈ L := hKL hk
  simpa only [inv_mul_cancel_right] using L.mul_mem hd hl

theorem normal_generating_pairs_of_cyclic_kernel_normal_total
    {G Q : Type} [Group G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) [IsCyclic f.ker]
    (hQ : ∀ A B : Subgroup Q, A.Normal → B.Normal → A ≤ B ∨ B ≤ A) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin 2 → G, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_cyclic_kernel_normal_generators f hf
    (normal_generating_singletons_of_finite_normal_total hQ)

theorem quotientSocle_two_of_cyclic_kernel_normal_total
    {G Q : Type} [Group G] [Group Q] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) [IsCyclic f.ker]
    (hQ : ∀ A B : Subgroup Q, A.Normal → B.Normal → A ≤ B ∨ B ≤ A)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_pairs_of_cyclic_kernel_normal_total f hf hQ) N

end SymmetricSubgroupAsymptotics

end
