import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import SymmetricSubgroupAsymptotics.BinaryNormalRegistry

/-! Short actual ambient normal-generation certificates.  A word is a product
of conjugates of retained seeds.  Its finite evaluation is independently
checked; no normal-generator rank is a certificate premise. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords

variable {G : Type*} [Group G]

def eval {k : ℕ} (seed : Fin k → G) (w : List (G × Fin k)) : G :=
  (w.map (fun a => a.1 * seed a.2 * a.1⁻¹)).prod

theorem eval_mem {k : ℕ} (seed : Fin k → G) (w : List (G × Fin k)) :
    eval seed w ∈ Subgroup.normalClosure (Set.range seed) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hx
  exact (inferInstance : (Subgroup.normalClosure (Set.range seed)).Normal).conj_mem
    _ (Subgroup.subset_normalClosure (Set.mem_range_self a.2)) a.1

theorem normalGen_le_tuple {k : ℕ} (N : Subgroup G) [N.Normal]
    (seed : Fin k → G) (hseed : Subgroup.normalClosure (Set.range seed) = N) :
    MarkedC4.normalGen N ≤ k := by
  let s : Finset G := Finset.univ.image seed
  have hs : (s : Set G) = Set.range seed := by
    ext x
    simp [s]
  have hmem : (s : Set G) ⊆ N := by
    rw [hs, ← hseed]
    exact Subgroup.subset_normalClosure
  have hcl : Subgroup.normalClosure (s : Set G) = N := by rw [hs, hseed]
  exact (MarkedC4.normalGen_le hmem hcl).trans
    (Finset.card_image_le.trans_eq (Finset.card_fin k))

theorem normalGen_le_of_closure_tuple {r : ℕ}
    (N : Subgroup G) [N.Normal] (generators : Fin r → G)
    (hgen : Subgroup.closure (Set.range generators) = N) :
    MarkedC4.normalGen N ≤ r := by
  apply normalGen_le_tuple N generators
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rw [← hgen]
    exact Subgroup.subset_closure
  · rw [← hgen]
    exact Subgroup.closure_le_normalClosure

theorem normalGen_le_of_words {r k : ℕ}
    (N : Subgroup G) [N.Normal] (generators : Fin r → G)
    (hgen : Subgroup.closure (Set.range generators) = N)
    (selected : Fin k → Fin r) (words : Fin r → List (G × Fin k))
    (checked : ∀ j, eval (generators ∘ selected) (words j) = generators j) :
    MarkedC4.normalGen N ≤ k := by
  apply normalGen_le_tuple N (generators ∘ selected)
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    rw [← hgen]
    exact Subgroup.subset_closure (Set.mem_range_self (selected i))
  · rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    rw [← checked j]
    exact eval_mem _ _

end SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords

end
