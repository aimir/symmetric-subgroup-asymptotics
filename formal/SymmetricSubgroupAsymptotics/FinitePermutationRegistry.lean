import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import SymmetricSubgroupAsymptotics.BinarySylowCoverage

/-!
# Soundness of finite row-mask action registries

This small-domain checker enumerates subsets of a certified literal action.
It is useful for end-to-end registry tests; large registries instead use
index-prime transitions. Both routes conclude equality of actual original
permutation subgroups, not equality of abstract group identifiers.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {w n : ℕ} {ι I : Type*} {generators : ι → Equiv.Perm (Fin w)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)

def encodedRowAction (i : Fin n) (x : Fin w) : Fin w :=
  finFunctionFinEquiv.symm (C.rows i) x

theorem encodedRowAction_eq (i : Fin n) (x : Fin w) :
    encodedRowAction C i x = C.toCayley.elements i x := by
  have h := C.encode_elements i
  change permutationCode (C.toCayley.elements i) = C.rows i at h
  rw [encodedRowAction, ← h, permutationCode]
  exact congrFun (finFunctionFinEquiv.symm_apply_apply _) x

/-- A checked row-mask classification covers every actual transitive
subgroup of the original generated permutation action. -/
theorem permutation_registry_of_row_masks
    (actions : I → Subgroup (Equiv.Perm (Fin w)))
    (masks : I → Fin n → Bool)
    (hmask : ∀ k i, masks k i = true ↔ C.toCayley.elements i ∈ actions k)
    (hactions : ∀ k, actions k ≤ Subgroup.closure (Set.range generators))
    (base : Fin w)
    (checked : ∀ selected : Fin n → Bool,
      selected C.identity = true →
      (∀ i j, selected i = true → selected j = true →
        selected (C.rowMul i j) = true) →
      (∀ y : Fin w, ∃ i, selected i = true ∧ encodedRowAction C i base = y) →
      ∃ k, ∀ i, selected i = masks k i)
    (K : Subgroup (Equiv.Perm (Fin w)))
    (hK : K ≤ Subgroup.closure (Set.range generators))
    (htrans : PermutationSubgroupTransitive K) : ∃ k, K = actions k := by
  classical
  let selected : Fin n → Bool := fun i => decide (C.toCayley.elements i ∈ K)
  have hsel : ∀ i, selected i = true ↔ C.toCayley.elements i ∈ K := by
    intro i
    exact decide_eq_true_iff
  obtain ⟨k, hk⟩ := checked selected
    ((hsel C.identity).mpr (by
      change C.toCayley.elements C.toCayley.identity ∈ K
      rw [C.toCayley.identity_eq]
      exact K.one_mem))
    (fun i j hi hj => (hsel _).mpr (by
      rw [C.elements_mul]
      exact K.mul_mem ((hsel _).mp hi) ((hsel _).mp hj)))
    (fun y => by
      obtain ⟨g, hg, hgy⟩ := htrans base y
      obtain ⟨i, hi⟩ := (C.toCayley.mem_closure_iff g).mp (hK hg)
      exact ⟨i, (hsel i).mpr (hi ▸ hg), by rw [encodedRowAction_eq, hi, hgy]⟩)
  refine ⟨k, le_antisymm ?_ ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := (C.toCayley.mem_closure_iff g).mp (hK hg)
    exact (hmask k i).mp ((hk i) ▸ (hsel i).mpr hg)
  · intro g hg
    obtain ⟨i, rfl⟩ := (C.toCayley.mem_closure_iff g).mp (hactions k hg)
    exact (hsel i).mp ((hk i).symm ▸ (hmask k i).mpr hg)

end SymmetricSubgroupAsymptotics
