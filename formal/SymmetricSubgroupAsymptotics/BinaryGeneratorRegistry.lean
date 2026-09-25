import SymmetricSubgroupAsymptotics.BinaryCharacterRegistry
import SymmetricSubgroupAsymptotics.BinaryGeneratorConjugacy

/-!
# Generator-sized checked conjugacy edges

Two-way row correspondences are unnecessary for index-two children.
Membership of inverse-conjugated target generators gives inclusion, and
exact checked cardinalities force equality. This reduces each edge to a
few original generator membership witnesses.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

structure GeneratedPermutationRegistry {w : ℕ} {I : Type*}
    (actions : I → Subgroup (Equiv.Perm (Fin w))) where
  generatorCount : I → ℕ
  generators : ∀ k, Fin (generatorCount k) → Equiv.Perm (Fin w)
  generated_eq : ∀ k, actions k = Subgroup.closure (Set.range (generators k))
  order : I → ℕ
  card_eq : ∀ k, Nat.card (actions k) = order k

variable {w n : ℕ} {ι I : Type*} {generators : ι → Equiv.Perm (Fin w)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)
    (B : BinaryRowCharacters C)
    (actions : I → Subgroup (Equiv.Perm (Fin w)))
    (R : GeneratedPermutationRegistry actions)

/-- Complete actual index-two child coverage from generator-sized edges. -/
theorem binary_generator_registry_children
    (hinj : Function.Injective C.rows) (base : Fin w)
    (checked : ∀ bits : ι → Bool,
      (∃ j, bits j = false) →
      (∀ i j, B.values bits (C.next i j) = (B.values bits i == bits j)) →
      (∀ y : Fin w, ∃ i, B.values bits i = true ∧ encodedRowAction C i base = y) →
      ∃ k, ∃ g : Equiv.Perm (Fin w), R.order k * 2 = n ∧
        ∀ j, ∃ i, B.values bits i = true ∧
          C.rows i = permutationCode (MulAut.conj g⁻¹ (R.generators k j)))
    (K : Subgroup (Equiv.Perm (Fin w)))
    (hK : K ≤ Subgroup.closure (Set.range generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range generators)) = 2)
    (htrans : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K := by
  classical
  let bits : ι → Bool := fun j => decide (generators j ∈ K)
  have hbits : ∀ j, bits j = true ↔ generators j ∈ K := fun _ => decide_eq_true_iff
  have hnontriv : ∃ j, bits j = false := by
    by_contra hn
    have hle : Subgroup.closure (Set.range generators) ≤ K := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j,rfl⟩
      apply (hbits j).mp
      cases hj : bits j
      · exact (hn ⟨j,hj⟩).elim
      · rfl
    have hone := Subgroup.relIndex_eq_one.mpr hle
    rw [hindex] at hone
    omega
  have hmem := B.membership_iff C K hindex bits hbits
  obtain ⟨k,g,hcard,hgens⟩ := checked bits hnontriv
    (B.transition_eq C K hindex bits hbits)
    (fun y => by
      obtain ⟨h,hh,hxy⟩ := htrans base y
      obtain ⟨i,hi⟩ := (C.toCayley.mem_closure_iff h).mp (hK hh)
      exact ⟨i,(hmem i).mpr (hi ▸ hh), by rw [encodedRowAction_eq, hi, hxy]⟩)
  refine ⟨k,g,?_⟩
  rw [R.generated_eq]
  apply binary_generator_conjugacy (R.generators k) g hK hindex
  · rw [← R.generated_eq, R.card_eq, C.card_closure hinj]
    exact hcard
  · intro j
    obtain ⟨i,hi,hcode⟩ := hgens j
    have he : C.toCayley.elements i = MulAut.conj g⁻¹ (R.generators k j) := by
      apply permutationCode_injective
      exact (C.encode_elements i).trans hcode
    exact he ▸ (hmem i).mp hi

end SymmetricSubgroupAsymptotics
