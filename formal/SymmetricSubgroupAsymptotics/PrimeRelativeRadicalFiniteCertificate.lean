import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalFiniteGenerators
import SymmetricSubgroupAsymptotics.FiniteGeneratorNormality
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Small finite certificates for the relative radical in the original
ambient group. Candidate generators must actually lie in the radical;
whole-ambient normality and the finite power/commutator tests give the
reverse containment. No ambient or normal-subgroup enumeration is used. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G ι κ τ : Type*} [Group G]

structure PrimeRelativeRadicalFiniteCertificate
    (N : Subgroup G) [N.Normal] (ambient : ι → G)
    (generators : κ → G) (candidate : τ → G) (n : ℕ) where
  cayley : FiniteCayleyCertificate candidate n
  rows_injective : Function.Injective cayley.elements
  candidate_mem : ∀ j, candidate j ∈ primeRelativeRadical p N
  conjugateRow : ι → τ → Fin n
  conjugate_eq : ∀ i j, cayley.elements (conjugateRow i j) =
    ambient i * candidate j * (ambient i)⁻¹
  powerRow : κ → Fin n
  power_eq : ∀ j, cayley.elements (powerRow j) = generators j ^ p
  mixedRow : κ → ι → Fin n
  mixed_eq : ∀ j i, cayley.elements (mixedRow j i) = ⁅generators j, ambient i⁆

namespace PrimeRelativeRadicalFiniteCertificate

variable {p} [Finite G] {N : Subgroup G} [N.Normal]
    {ambient : ι → G} {generators : κ → G} {candidate : τ → G} {n : ℕ}
    (C : PrimeRelativeRadicalFiniteCertificate p N ambient generators candidate n)

include C

theorem normal (hambient : Subgroup.closure (Set.range ambient) = ⊤) :
    (Subgroup.closure (Set.range candidate)).Normal := by
  have h := generated_le_normalizer_of_generator_conjugates candidate ambient
    (fun i j => (C.cayley.mem_closure_iff _).mpr
      ⟨C.conjugateRow i j, C.conjugate_eq i j⟩)
  rw [hambient] at h
  exact Subgroup.normalizer_eq_top_iff.mp (top_unique h)

theorem closure_eq_radical
    (hambient : Subgroup.closure (Set.range ambient) = ⊤)
    (hgenerators : Subgroup.closure (Set.range generators) = N) :
    Subgroup.closure (Set.range candidate) = primeRelativeRadical p N := by
  letI := C.normal hambient
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact C.candidate_mem j
  · apply primeRelativeRadical_le_of_finite_generator_tests p N
      ambient hambient generators hgenerators
    · intro j
      exact (C.cayley.mem_closure_iff _).mpr ⟨C.powerRow j, C.power_eq j⟩
    · intro j i
      exact (C.cayley.mem_closure_iff _).mpr ⟨C.mixedRow j i, C.mixed_eq j i⟩

theorem card_radical
    (hambient : Subgroup.closure (Set.range ambient) = ⊤)
    (hgenerators : Subgroup.closure (Set.range generators) = N) :
    Nat.card (primeRelativeRadical p N) = n := by
  rw [← C.closure_eq_radical hambient hgenerators]
  exact C.cayley.card_closure C.rows_injective

end PrimeRelativeRadicalFiniteCertificate
end SymmetricSubgroupAsymptotics
