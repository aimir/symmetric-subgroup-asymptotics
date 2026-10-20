import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles
import Mathlib.Data.Fin.Tuple.Basic

/-! Uniform normal generation for a genuine subdirect pair. Both
coordinate maps must be onto and their pair must be injective. The normal
subgroup may be diagonal, a fibre product, or otherwise correlated. No
normal-generator bound is inherited merely from an ambient overgroup. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem normal_generating_tuples_subdirect_pair
    {G L R : Type} [Group G] [Group L] [Group R] {a b : ℕ}
    (f : G →* L) (g : G →* R)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hjoint : Function.Injective (fun x : G => (f x, g x)))
    (hL : ∀ N : Subgroup L, N.Normal →
      ∃ x : Fin a → L, Subgroup.normalClosure (Set.range x) = N)
    (hR : ∀ N : Subgroup R, N.Normal →
      ∃ x : Fin b → R, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup G, N.Normal →
      ∃ x : Fin (a + b) → G, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI : N.Normal := hN
  let K : Subgroup G := N ⊓ f.ker
  letI : K.Normal := inferInstance
  obtain ⟨x, hx⟩ := hL (N.map f) (hN.map f hf)
  obtain ⟨y, hy⟩ := hR (K.map g) ((inferInstance : K.Normal).map g hg)
  have hxN : ∀ i, ∃ z : G, z ∈ N ∧ f z = x i := by
    intro i
    have h : x i ∈ N.map f := by
      rw [← hx]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact h
  have hyK : ∀ i, ∃ z : G, z ∈ K ∧ g z = y i := by
    intro i
    have h : y i ∈ K.map g := by
      rw [← hy]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    exact h
  choose u huN hu using hxN
  choose v hvK hv using hyK
  let z : Fin (a + b) → G := Fin.addCases u v
  let C : Subgroup G := Subgroup.normalClosure (Set.range z)
  letI : C.Normal := by dsimp [C]; infer_instance
  have huC (i : Fin a) : u i ∈ C := by
    have h := Subgroup.subset_normalClosure (Set.mem_range_self (f := z) (i.castAdd b))
    simpa only [z, Fin.addCases_left] using h
  have hvC (i : Fin b) : v i ∈ C := by
    have h := Subgroup.subset_normalClosure (Set.mem_range_self (f := z) (i.natAdd a))
    simpa only [z, Fin.addCases_right] using h
  have hCN : C ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [z, Fin.addCases_left] using huN j
    · intro j
      simpa only [z, Fin.addCases_right] using (hvK j).1
  have hkernelImage : K.map g ≤ (C ⊓ f.ker).map g := by
    letI : ((C ⊓ f.ker).map g).Normal := Subgroup.Normal.map inferInstance g hg
    rw [← hy]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, ⟨hvC i, (hvK i).2⟩, hv i⟩
  have hKC : K ≤ C := by
    intro n hn
    obtain ⟨c, hc, he⟩ := hkernelImage (show g n ∈ K.map g from ⟨n, hn, rfl⟩)
    have hcn : c = n := hjoint (Prod.ext (hc.2.trans hn.2.symm) he)
    exact hcn ▸ hc.1
  have himage : N.map f ≤ C.map f := by
    letI : (C.map f).Normal := Subgroup.Normal.map inferInstance f hf
    rw [← hx]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact ⟨u i, huC i, hu i⟩
  refine ⟨z, le_antisymm hCN ?_⟩
  intro n hn
  obtain ⟨c, hc, he⟩ := himage (show f n ∈ N.map f from ⟨n, hn, rfl⟩)
  have hd : n * c⁻¹ ∈ K := by
    refine ⟨N.mul_mem hn (N.inv_mem (hCN hc)), ?_⟩
    change f (n * c⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hprod := C.mul_mem (hKC hd) hc
  simpa only [inv_mul_cancel_right] using hprod

/-- The bound controls every quotient of the original subdirect group. -/
theorem quotientSocle_of_subdirect_pair_normal_generators
    {G L R : Type} [Group G] [Group L] [Group R] {a b : ℕ}
    (f : G →* L) (g : G →* R)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hjoint : Function.Injective (fun x : G => (f x, g x)))
    (hL : ∀ N : Subgroup L, N.Normal →
      ∃ x : Fin a → L, Subgroup.normalClosure (Set.range x) = N)
    (hR : ∀ N : Subgroup R, N.Normal →
      ∃ x : Fin b → R, Subgroup.normalClosure (Set.range x) = N)
    (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) (a + b) :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples_subdirect_pair f g hf hg hjoint hL hR) N

end SymmetricSubgroupAsymptotics

end
