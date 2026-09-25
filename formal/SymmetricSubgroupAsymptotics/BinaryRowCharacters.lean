import SymmetricSubgroupAsymptotics.FinitePermutationRegistry

/-!
# Index-two subgroups are determined by original-generator bits

A registry can enumerate the at most 2^d generator-bit assignments instead
of all subsets of its |U| certified rows. Checked parent equations force
the row mask of every actual index-two subgroup; inconsistent assignments
are rejected by the original-generator transition equations.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι Code : Type*} [Group G] {generators : ι → G}
    {E : GeneratorEncoding generators Code} {n : ℕ}

/-- Tables of candidate index-two kernels, with local BFS-parent equations.
The identity belongs to every candidate; a true generator bit means that
the generator belongs to its kernel. -/
structure BinaryRowCharacters (C : EncodedCayleyCertificate E n) where
  values : (ι → Bool) → Fin n → Bool
  identity_eq : ∀ bits, values bits C.identity = true
  parent_eq : ∀ bits i hi, values bits i =
    (values bits (C.parent i hi) == bits (C.letter i hi))

namespace BinaryRowCharacters

variable [Finite G] (C : EncodedCayleyCertificate E n) (B : BinaryRowCharacters C)

private theorem bool_eq_iff_true_iff (a b : Bool) :
    a = b ↔ (a = true ↔ b = true) := by cases a <;> cases b <;> decide

/-- Every actual relative-index-two subgroup has exactly one of the
candidate masks, determined by its original generator membership bits. -/
theorem membership_iff (K : Subgroup G)
    (hindex : K.relIndex (Subgroup.closure (Set.range generators)) = 2)
    (bits : ι → Bool) (hbits : ∀ j, bits j = true ↔ generators j ∈ K)
    (i : Fin n) : B.values bits i = true ↔ C.toCayley.elements i ∈ K := by
  let U := Subgroup.closure (Set.range generators)
  have hiU : ∀ r, C.toCayley.elements r ∈ U := fun r =>
    (C.toCayley.mem_closure_iff _).mpr ⟨r,rfl⟩
  have hgU : ∀ j, generators j ∈ U := fun j =>
    Subgroup.subset_closure (Set.mem_range_self j)
  by_cases hi : i = C.identity
  · subst i
    rw [B.identity_eq]
    change true = true ↔ C.toCayley.elements C.toCayley.identity ∈ K
    simp only [C.toCayley.identity_eq, K.one_mem]
  · have hmul := (K.subgroupOf U).mul_mem_iff_of_index_two hindex
      (a := ⟨C.toCayley.elements (C.parent i hi),hiU _⟩)
      (b := ⟨generators (C.letter i hi),hgU _⟩)
    change C.toCayley.elements (C.parent i hi) * generators (C.letter i hi) ∈ K ↔ _ at hmul
    have he : C.toCayley.elements i =
        C.toCayley.elements (C.parent i hi) * generators (C.letter i hi) := by
      have hh := C.toCayley.next_eq (C.parent i hi) (C.letter i hi)
      change C.toCayley.elements (C.next _ _) = _ at hh
      rw [C.parent_next] at hh
      exact hh
    rw [B.parent_eq bits i hi, beq_iff_eq, bool_eq_iff_true_iff,
      membership_iff K hindex bits hbits (C.parent i hi), hbits, he, hmul]
    rfl
termination_by C.rank i
decreasing_by exact C.parent_lt i hi

/-- Only local generator equations need be used to reject unrealizable
assignments: every actual index-two subgroup automatically passes them. -/
theorem transition_eq (K : Subgroup G)
    (hindex : K.relIndex (Subgroup.closure (Set.range generators)) = 2)
    (bits : ι → Bool) (hbits : ∀ j, bits j = true ↔ generators j ∈ K)
    (i : Fin n) (j : ι) :
    B.values bits (C.next i j) = (B.values bits i == bits j) := by
  apply (bool_eq_iff_true_iff _ _).mpr
  rw [B.membership_iff C K hindex bits hbits, beq_iff_eq,
    bool_eq_iff_true_iff, B.membership_iff C K hindex bits hbits, hbits]
  change C.toCayley.elements (C.toCayley.next i j) ∈ K ↔ _
  rw [C.toCayley.next_eq]
  exact (K.subgroupOf (Subgroup.closure (Set.range generators))).mul_mem_iff_of_index_two
    hindex
    (a := ⟨C.toCayley.elements i,(C.toCayley.mem_closure_iff _).mpr ⟨i,rfl⟩⟩)
    (b := ⟨generators j,Subgroup.subset_closure (Set.mem_range_self j)⟩)

end BinaryRowCharacters
end SymmetricSubgroupAsymptotics
