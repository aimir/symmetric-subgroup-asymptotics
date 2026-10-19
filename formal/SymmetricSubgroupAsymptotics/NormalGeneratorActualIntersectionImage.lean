import SymmetricSubgroupAsymptotics.NormalGeneratorExtension
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-! Normal-generator addition for the actual intersection and image of
one fixed original normal subgroup. No uniform image bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuple_of_actual_intersection_and_image
    {G Q : Type} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f) {a b : ℕ}
    (N : Subgroup G) [N.Normal]
    (hK : ∃ x : Fin a → G, Subgroup.normalClosure (Set.range x)=N ⊓ f.ker)
    (hQ : ∃ y : Fin b → Q, Subgroup.normalClosure (Set.range y)=N.map f) :
    ∃ z : Fin (a+b) → G, Subgroup.normalClosure (Set.range z)=N := by
  let hN : N.Normal := inferInstance
  let K : Subgroup G := N ⊓ f.ker
  obtain ⟨x, hx⟩ := hK
  change Subgroup.normalClosure (Set.range x)=K at hx
  have hxK (i : Fin a) : x i ∈ K := by
    rw [← hx]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  obtain ⟨y, hy⟩ := hQ
  have hlift : ∀ i, ∃ z : G, z ∈ N ∧ f z = y i := by
    intro i
    have hi : y i ∈ N.map f := by
      rw [← hy]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact hi
  choose z hzN hz using hlift
  let u : Fin (a + b) → G := Fin.addCases x z
  let L := Subgroup.normalClosure (Set.range u)
  letI : L.Normal := by dsimp [L]; infer_instance
  have hxL (i : Fin a) : x i ∈ L := by
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
      simpa only [u,Fin.addCases_left] using (hxK j).1
    · intro j
      simpa only [u, Fin.addCases_right] using hzN j
  have hKL : K ≤ L := by
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
  have hk : n*l⁻¹∈K := ⟨N.mul_mem hn (N.inv_mem (hLN hl)),hker⟩
  have hd : n * l⁻¹ ∈ L := hKL hk
  simpa only [inv_mul_cancel_right] using L.mul_mem hd hl

theorem normalGen_le_actual_intersection_add_image
    {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal]
    (a b : ℕ) (hK : MarkedC4.normalGen (N ⊓ f.ker)≤a)
    (hQ : MarkedC4.normalGen (N.map f)≤b) : MarkedC4.normalGen N≤a+b := by
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  obtain ⟨x,hx⟩ := exists_normal_generating_tuple_of_normalGen_le (N ⊓ f.ker) hK
  obtain ⟨y,hy⟩ := exists_normal_generating_tuple_of_normalGen_le (N.map f) hQ
  obtain ⟨z,hz⟩ := normal_generating_tuple_of_actual_intersection_and_image f hf N ⟨x,hx⟩ ⟨y,hy⟩
  exact normalGen_le_of_fin_tuple z hz

end SymmetricSubgroupAsymptotics
