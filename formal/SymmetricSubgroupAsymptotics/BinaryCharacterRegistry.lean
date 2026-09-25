import SymmetricSubgroupAsymptotics.BinaryRowCharacters

/-!
# Literal conjugacy edges from binary-character row tables

Generator-bit enumeration and two-way code-row correspondences install
all transitive index-two children. Every conjugator acts on the original
points. The resulting theorem has exactly the local-child interface used
by the global Sylow registry theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

/-- Numeric enumeration of all original-generator membership assignments. -/
def binaryAssignment {d : ℕ} (c : Fin (2^d)) (j : Fin d) : Bool :=
  finTwoEquiv (finFunctionFinEquiv.symm c j)

theorem binaryAssignment_surjective (d : ℕ) : Function.Surjective (@binaryAssignment d) := by
  intro bits
  refine ⟨finFunctionFinEquiv (fun j => finTwoEquiv.symm (bits j)), ?_⟩
  funext j
  simp only [binaryAssignment, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Conjugation of a numeric original-point image row. -/
def permutationConjugateCode {w : ℕ} (g : Equiv.Perm (Fin w)) (c : Fin (w^w)) :
    Fin (w^w) := finFunctionFinEquiv (fun x => g (finFunctionFinEquiv.symm c (g⁻¹ x)))

theorem permutationCode_conjugate {w : ℕ} (g h : Equiv.Perm (Fin w)) :
    permutationCode (MulAut.conj g h) = permutationConjugateCode g (permutationCode h) := by
  unfold permutationCode permutationConjugateCode
  congr 1
  funext x
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Any supplied action registry can expose its exact original code rows,
independently of how each action was certified. -/
structure LiteralPermutationRegistry {w : ℕ} {I : Type*}
    (actions : I → Subgroup (Equiv.Perm (Fin w))) where
  size : I → ℕ
  rows : ∀ k, Fin (size k) → Fin (w^w)
  mem_iff : ∀ k h, h ∈ actions k ↔ ∃ j, rows k j = permutationCode h

variable {w n : ℕ} {ι I : Type*} {generators : ι → Equiv.Perm (Fin w)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)
    (B : BinaryRowCharacters C)
    (actions : I → Subgroup (Equiv.Perm (Fin w)))
    (R : LiteralPermutationRegistry actions)

/-- Soundness of scalable original-generator bit enumeration. Every actual
transitive relative-index-two subgroup is identified by an actual ambient
conjugator and an exact two-way correspondence of original code rows. -/
theorem binary_character_registry_children
    (base : Fin w)
    (checked : ∀ bits : ι → Bool,
      (∀ i j, B.values bits (C.next i j) = (B.values bits i == bits j)) →
      (∀ y : Fin w, ∃ i, B.values bits i = true ∧ encodedRowAction C i base = y) →
      ∃ k, ∃ g : Equiv.Perm (Fin w),
        (∀ i, B.values bits i = true →
          ∃ j, R.rows k j = permutationConjugateCode g (C.rows i)) ∧
        (∀ j, ∃ i, B.values bits i = true ∧
          R.rows k j = permutationConjugateCode g (C.rows i)))
    (K : Subgroup (Equiv.Perm (Fin w)))
    (hK : K ≤ Subgroup.closure (Set.range generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range generators)) = 2)
    (htrans : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K := by
  classical
  let bits : ι → Bool := fun j => decide (generators j ∈ K)
  have hbits : ∀ j, bits j = true ↔ generators j ∈ K := fun _ => decide_eq_true_iff
  have hmem := B.membership_iff C K hindex bits hbits
  obtain ⟨k,g,hforward,hbackward⟩ := checked bits
    (B.transition_eq C K hindex bits hbits)
    (fun y => by
      obtain ⟨h,hh,hxy⟩ := htrans base y
      obtain ⟨i,hi⟩ := (C.toCayley.mem_closure_iff h).mp (hK hh)
      exact ⟨i,(hmem i).mpr (hi ▸ hh), by rw [encodedRowAction_eq, hi, hxy]⟩)
  have hcode : ∀ i, permutationCode (MulAut.conj g (C.toCayley.elements i)) =
      permutationConjugateCode g (C.rows i) := by
    intro i
    rw [permutationCode_conjugate]
    congr 1
    exact C.encode_elements i
  refine ⟨k,g,?_⟩
  rw [Subgroup.pointwise_smul_def]
  apply le_antisymm
  · rintro _ ⟨h,hh,rfl⟩
    obtain ⟨i,hi⟩ := (C.toCayley.mem_closure_iff h).mp (hK hh)
    obtain ⟨j,hj⟩ := hforward i ((hmem i).mpr (hi ▸ hh))
    apply (R.mem_iff k _).mpr
    refine ⟨j, ?_⟩
    change R.rows k j = permutationCode (MulAut.conj g h)
    rw [← hi, hcode]
    exact hj
  · intro h hh
    obtain ⟨j,hj⟩ := (R.mem_iff k h).mp hh
    obtain ⟨i,hi,hij⟩ := hbackward j
    refine ⟨C.toCayley.elements i,(hmem i).mp hi,?_⟩
    apply permutationCode_injective
    change permutationCode (MulAut.conj g (C.toCayley.elements i)) = permutationCode h
    rw [hcode, ← hij, hj]

end SymmetricSubgroupAsymptotics
