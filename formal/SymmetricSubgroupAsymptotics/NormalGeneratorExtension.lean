import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
import Mathlib.Data.Fin.Tuple.Basic

/-! Uniform ambient normal-generator bounds add across a surjective homomorphism.
The kernel bound is measured inside the kernel, so its generators also cover
the intersection with any normal subgroup of the original group. No finite,
split, cyclic, or centrality assumption is needed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuples_of_kernel_and_image
    {G Q : Type} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) {a b : ℕ}
    (hK : ∀ K : Subgroup f.ker, K.Normal →
      ∃ x : Fin a → f.ker, Subgroup.normalClosure (Set.range x) = K)
    (hQ : ∀ M : Subgroup Q, M.Normal →
      ∃ y : Fin b → Q, Subgroup.normalClosure (Set.range y) = M) :
    ∀ N : Subgroup G, N.Normal →
      ∃ z : Fin (a + b) → G, Subgroup.normalClosure (Set.range z) = N := by
  intro N hN
  letI := hN
  let ι : f.ker →* G := f.ker.subtype
  let K : Subgroup f.ker := N.comap ι
  obtain ⟨x, hx⟩ := hK K (hN.comap ι)
  have hxK (i : Fin a) : x i ∈ K := by
    rw [← hx]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  obtain ⟨y, hy⟩ := hQ (N.map f) (hN.map f hf)
  have hlift : ∀ i, ∃ z : G, z ∈ N ∧ f z = y i := by
    intro i
    have hi : y i ∈ N.map f := by
      rw [← hy]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact hi
  choose z hzN hz using hlift
  let u : Fin (a + b) → G := Fin.addCases (fun i ↦ ι (x i)) z
  let L := Subgroup.normalClosure (Set.range u)
  letI : L.Normal := by dsimp [L]; infer_instance
  have hxL (i : Fin a) : ι (x i) ∈ L := by
    have hh := Subgroup.subset_normalClosure
      (Set.mem_range_self (f := u) (i.castAdd b))
    simpa only [u, Fin.addCases_left] using hh
  have hzL (i : Fin b) : z i ∈ L := by
    have hh := Subgroup.subset_normalClosure
      (Set.mem_range_self (f := u) (i.natAdd a))
    simpa only [u, Fin.addCases_right] using hh
  have hLN : L ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [u, Fin.addCases_left] using hxK j
    · intro j
      simpa only [u, Fin.addCases_right] using hzN j
  have hKL : K ≤ L.comap ι := by
    letI : (L.comap ι).Normal := (inferInstance : L.Normal).comap ι
    rw [← hx]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact hxL i
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

theorem quotientSocle_of_kernel_and_image
    {G Q : Type} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) {a b : ℕ}
    (hK : ∀ K : Subgroup f.ker, K.Normal →
      ∃ x : Fin a → f.ker, Subgroup.normalClosure (Set.range x) = K)
    (hQ : ∀ M : Subgroup Q, M.Normal →
      ∃ y : Fin b → Q, Subgroup.normalClosure (Set.range y) = M)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) (a + b) :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples_of_kernel_and_image f hf hK hQ) N

end SymmetricSubgroupAsymptotics

end
